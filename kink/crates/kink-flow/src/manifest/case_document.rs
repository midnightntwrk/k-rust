//! A case document a `cases` pattern matched: one case, or named cases (the krs case document,
//! read here with kink's containment rule).
//!
//! A document of one case holds `inputs`, `expect`, `expect_for` and `provenance` at its top. A
//! document of named cases holds `case`, the list of its cases: an array (TOML's `[[case]]` tables)
//! of named cases, each a table of `name`, `inputs`, `expect`, `expect_for` and `provenance`, and
//! of includes, `{ "$data-file" = "path" }`, each naming a
//! `.toml` or `.json` file whose document is a list (an array, or a table whose one key is
//! `case`, as TOML writes a list), whose cases stand at the include's place; `case` may itself be
//! an include. A path an included file names, an include's or one in a case's values, is
//! relative to that file; every file is read inside the flow's case root (the root `[corpus]`
//! names, else the manifest's directory: [`CaseRoot`]) by the rule a program file is read by, and a file that includes itself, directly or through others, is
//! refused naming the cycle. A name is a nonempty string no other case of the document has, the
//! included files' cases included, so that the document's path and the name identify the case
//! (`<path>#<name>`).
//!
//! A case's `run`, how a tool runs it on its own, is refused, in a case and at the top of a
//! document of named cases: kink runs every program of a corpus as the corpus says (`[stop]`,
//! the entry's `stop_count`, `[budget]`), and a second statement of where a run ends would make
//! the ends kink compares those of another observation than the one the case document states.
//!
//! A case's `provenance`, `{ found_by, reason }`, says which tool or person found it and why it is
//! in the corpus ([`Provenance`]): each member optional and a nonempty string, at least one given,
//! and no other member. It is read as written and changes no run: a report shows it, and no digest
//! or key holds it.
//!
//! A case's `expect_for` scopes expectations to definitions: a nonempty table whose keys are
//! nonempty definition names (the flow's [`super::SpecDecl::expect_scope`]: a K corpus's main
//! module, a KRS corpus's facet), each value a table, the expected end, which the reader keeps as
//! written and reads no member of, as it reads none of `expect`. A flow checks `expect` and the
//! expectation `expect_for` scopes to its own definition (`crate::expect`).
//!
//! A case read by a front end's decoder (a flow of `[spec] krs`) has typed inputs, which are never
//! parsed, so neither its `expect` nor a scoped one holds `rejected`, which is refused at its
//! position: that a program must be rejected before it runs is stated on a `[[program]]` or
//! `files` entry (`expect = { rejected = "parse" }`), whose program text kink parses.
//!
//! A case of a flow with a K declaration ([`CaseLevel::K`]) binds configuration variables to K
//! texts at the K level (`crate::admit`, "Case documents at the K level"): `[inputs]` by variable
//! name, `PGM` the program text. Its texts are parsed, so its `expect` may state that the case is
//! rejected before it runs, in the one form a `[[program]]` states it (`expect = { rejected =
//! "parse" }` or `"input"`, nothing beside it), and it may give `start_sort`, the sort its
//! program text is read at, where `[inputs]` binds `PGM`. A scoped expectation holds no
//! `rejected` at either level.

use super::{CaseRoot, ManifestError, Provenance, RejectedStage, join, program_key};
use crate::admit::{InputFiles, ManifestFiles};
use std::{collections::BTreeMap, fs, path::Path};
use toml::{Table, Value};

/// Why a case's `run` is refused (module documentation).
const RUN_REFUSED: &str = "kink runs every program as the corpus says ([stop], the entry's \
     `stop_count`, [budget]), so it reads no case's `run`: remove it, and state the rules a run \
     stops at under [stop] and the count in `stop_count`";

/// Why the `run` table `run` is refused ([`RUN_REFUSED`]), and when it holds a stop condition
/// (`stop_when`), that the corpus states it, as `[stop] when`, for every program alike.
fn run_refused(run: Option<&Value>) -> String {
    if run
        .and_then(Value::as_table)
        .is_some_and(|run| run.contains_key("stop_when"))
    {
        format!(
            "{RUN_REFUSED}; its `stop_when` is a stop condition, which the corpus states as \
             `[stop] when`"
        )
    } else {
        RUN_REFUSED.to_owned()
    }
}

/// Whose case documents a flow reads, which decides the keys a case may give (module
/// documentation).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CaseLevel {
    /// A flow with a K declaration: a case may also give `start_sort` and `expect = { rejected =
    /// STAGE }`, since its inputs are K texts at the K level.
    K,
    /// A flow of `[spec] krs`: the krs case document, the keys krs-exec's case table reads.
    Krs,
}

impl CaseLevel {
    /// The keys of a case at this level, besides a named case's `name`.
    fn keys(self) -> &'static [&'static str] {
        match self {
            Self::K => &K_CASE_KEYS,
            Self::Krs => &CASE_KEYS,
        }
    }

    /// The keys of a case as messages list them, `name` first for a named case.
    fn listed(self, named: bool) -> String {
        let keys = named
            .then_some("name")
            .into_iter()
            .chain(self.keys().iter().copied())
            .map(|key| format!("`{key}`"))
            .collect::<Vec<_>>();
        let (last, rest) = keys.split_last().expect("a case has keys");
        format!("{} and {last}", rest.join(", "))
    }
}

/// One case of a case document.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct DocumentCase {
    /// Its name, in a document of named cases; `None` for the one case of a document.
    pub(super) name: Option<String>,
    /// `inputs`: inputs by nonempty input name, kept as written (typed values for a front end's
    /// decoder, or K texts by configuration variable at the K level).
    pub(super) inputs: Table,
    /// `start_sort`: the sort the program text (`PGM` in `inputs`) is read at, in a flow with a
    /// K declaration only.
    pub(super) start_sort: Option<String>,
    /// `expect`: the end the case expects, kept as written; `None` where it states a rejection.
    pub(super) expect: Option<Table>,
    /// `expect = { rejected = STAGE }`: the case must be rejected before it runs, in a flow with
    /// a K declaration only.
    pub(super) rejected: Option<RejectedStage>,
    /// `expect_for`: the ends the case expects of a run on each definition it names, by
    /// definition name, each kept as written; empty without one.
    pub(super) expect_for: BTreeMap<String, Table>,
    /// `provenance`, when given.
    pub(super) provenance: Option<Provenance>,
    /// The name of the included file the case is written in, as [`InputFiles::read`] gives it
    /// (its path relative to the manifest's directory, links resolved); `None` for a case of the
    /// matched document itself.
    pub(super) file: Option<String>,
}

/// The cases of the case document `id` (a path relative to the canonical case root `root`),
/// which must resolve, links included, to a file inside `root`, in document order, read with the
/// keys of `level`.
pub(super) fn case_document(
    root: &CaseRoot,
    id: &str,
    level: CaseLevel,
) -> Result<Vec<DocumentCase>, ManifestError> {
    let key = program_key(id);
    let refused = |message: String| ManifestError::new(&key, message);
    let resolved = fs::canonicalize(root.directory.join(id))
        .map_err(|e| refused(format!("cannot read the case document: {e}")))?;
    let Ok(name) = resolved.strip_prefix(&root.directory) else {
        return Err(refused(format!("the case document escapes {}", root.name)));
    };
    let name = name.to_string_lossy().replace('\\', "/");
    let text = fs::read_to_string(&resolved)
        .map_err(|e| refused(format!("cannot read the case document: {e}")))?;
    let mut document: Table = toml::from_str(&text)
        .map_err(|e| refused(format!("the case document is no TOML document: {e}")))?;
    let Some(list) = document.remove("case") else {
        return one_case(document, &key, level).map(|case| vec![case]);
    };
    if let Some(other) = document.keys().next() {
        return Err(ManifestError::new(
            join(&key, other),
            if other == "run" {
                run_refused(document.get("run"))
            } else {
                format!(
                    "a document of named cases holds `case` only; one case's `{other}` belongs \
                     in its table in `case`"
                )
            },
        ));
    }
    let mut reader = CaseList {
        files: root.files(Some(id)),
        reading: vec![name],
        cases: Vec::new(),
        names: BTreeMap::new(),
        level,
    };
    reader.list(&list, &join(&key, "case"), None)?;
    if reader.cases.is_empty() {
        return Err(ManifestError::new(
            join(&key, "case"),
            "lists no case; a case document gives at least one program, as a pattern matches at \
             least one file",
        ));
    }
    Ok(reader.cases)
}

/// The keys of a krs case, besides a named case's `name`.
const CASE_KEYS: [&str; 4] = ["inputs", "expect", "expect_for", "provenance"];

/// The keys of a case of a flow with a K declaration, besides a named case's `name`.
const K_CASE_KEYS: [&str; 5] = ["inputs", "start_sort", "expect", "expect_for", "provenance"];

/// The one case of a document whose top is `document`, named `key`.
fn one_case(
    mut document: Table,
    key: &str,
    level: CaseLevel,
) -> Result<DocumentCase, ManifestError> {
    if let Some(other) = document
        .keys()
        .find(|other| !level.keys().contains(&other.as_str()))
    {
        let message = match other.as_str() {
            "run" => run_refused(document.get("run")),
            "name" => {
                "a document of one case names none; named cases are listed under `case`".to_owned()
            }
            _ => format!(
                "unknown key in a case document; a case has the keys {}",
                level.listed(false)
            ),
        };
        return Err(ManifestError::new(join(key, other), message));
    }
    let inputs = super::inputs(&document, key)?;
    let (expect, rejected) = expect(&mut document, key, level)?;
    Ok(DocumentCase {
        name: None,
        start_sort: start_sort(&document, &inputs, key)?,
        inputs,
        expect,
        rejected,
        expect_for: expect_for(&mut document, key, level)?,
        provenance: provenance(&mut document, key)?,
        file: None,
    })
}

/// `start_sort` of a case named `key` whose inputs are `inputs`, when given: a string, given only
/// where `inputs` binds the program text, `PGM` (only a flow with a K declaration reads the key).
fn start_sort(case: &Table, inputs: &Table, key: &str) -> Result<Option<String>, ManifestError> {
    let start_sort = super::optional_string(case, key, "start_sort")?;
    if start_sort.is_some() && !inputs.contains_key("PGM") {
        return Err(ManifestError::new(
            join(key, "start_sort"),
            "start_sort applies to the program text, `PGM` in `inputs`; this case has none",
        ));
    }
    Ok(start_sort)
}

/// Why a case's expectation holds no `rejected` (module documentation); krs-exec's case table
/// refuses it with the same text.
const REJECTED_IN_CASE: &str = "a case document's expectation states the end of its run: a \
     program that must be rejected before it runs is stated on a `[[program]]` or `files` entry \
     of the flow's manifest, `expect = { rejected = \"parse\" }` or `{ rejected = \"input\" }` \
     (a case document's typed inputs are never parsed)";

/// The expectation `expect` at `at`, refused where it holds `rejected` with `why`
/// ([`REJECTED_IN_CASE`], [`REJECTED_SCOPED`]).
fn no_rejected(expect: Table, at: &str, why: &str) -> Result<Table, ManifestError> {
    if expect.contains_key("rejected") {
        return Err(ManifestError::new(join(at, "rejected"), why));
    }
    Ok(expect)
}

/// The one form a case of a flow with a K declaration states a rejection in.
const REJECTED_CASE_FORM: &str = "a case that must be rejected before it runs states only that: \
     `expect = { rejected = \"parse\" }` (a K text it binds does not parse) or `{ rejected = \
     \"input\" }`, with no expected end beside it, since such a case has no run";

/// Why a scoped expectation of a case of a flow with a K declaration holds no `rejected` (module
/// documentation).
const REJECTED_SCOPED: &str = "a scoped expectation states the end of the case's run in that \
     definition's flows: a case whose K texts must be rejected before it runs states it in \
     `expect`, `expect = { rejected = \"parse\" }`";

/// `expect` of a case named `key`, when given: a table of the expected end without `rejected`,
/// or, at the K level, the one form a `[[program]]` states a rejection in (module
/// documentation), which gives the stage and no expected end.
fn expect(
    case: &mut Table,
    key: &str,
    level: CaseLevel,
) -> Result<(Option<Table>, Option<RejectedStage>), ManifestError> {
    if level == CaseLevel::K
        && case
            .get("expect")
            .and_then(Value::as_table)
            .is_some_and(|expect| expect.contains_key("rejected"))
    {
        let rejected = super::rejected_in(case, key, REJECTED_CASE_FORM)?;
        case.remove("expect");
        return Ok((None, rejected));
    }
    match case.remove("expect") {
        None => Ok((None, None)),
        Some(Value::Table(expect)) => no_rejected(expect, &join(key, "expect"), REJECTED_IN_CASE)
            .map(|expect| (Some(expect), None)),
        Some(_) => Err(ManifestError::new(
            join(key, "expect"),
            "expected a table of the expected end: `halt`, `rule`, `cells` and `compare`",
        )),
    }
}

/// `expect_for` of a case named `key`: a nonempty table of tables by nonempty definition name,
/// none holding `rejected`, when given (module documentation); empty when absent.
fn expect_for(
    case: &mut Table,
    key: &str,
    level: CaseLevel,
) -> Result<BTreeMap<String, Table>, ManifestError> {
    let rejected = match level {
        CaseLevel::K => REJECTED_SCOPED,
        CaseLevel::Krs => REJECTED_IN_CASE,
    };
    let at = join(key, "expect_for");
    let table = match case.remove("expect_for") {
        None => return Ok(BTreeMap::new()),
        Some(Value::Table(table)) => table,
        Some(_) => {
            return Err(ManifestError::new(
                at,
                "`expect_for` is a table of expected ends by definition name: \
                 `[expect_for.<definition>]`",
            ));
        }
    };
    if table.is_empty() {
        return Err(ManifestError::new(
            at,
            "scopes no expectation to a definition; give one, or remove `expect_for`",
        ));
    }
    table
        .into_iter()
        .map(|(definition, expect)| match expect {
            _ if definition.is_empty() => Err(ManifestError::new(
                join(&at, &definition),
                "a definition name is a nonempty string",
            )),
            Value::Table(expect) => no_rejected(expect, &join(&at, &definition), rejected)
                .map(|expect| (definition, expect)),
            _ => Err(ManifestError::new(
                join(&at, &definition),
                "an expectation scoped to a definition is a table of the expected end, as \
                 `expect` is",
            )),
        })
        .collect()
}

/// `provenance` of a case named `key`, when given: a table of `found_by` and `reason`, each a
/// nonempty string, at least one given (module documentation).
fn provenance(case: &mut Table, key: &str) -> Result<Option<Provenance>, ManifestError> {
    let at = join(key, "provenance");
    let table = match case.remove("provenance") {
        None => return Ok(None),
        Some(Value::Table(table)) => table,
        Some(_) => {
            return Err(ManifestError::new(
                at,
                "`provenance` is a table of `found_by` and `reason`, each a nonempty string",
            ));
        }
    };
    if let Some(other) = table
        .keys()
        .find(|other| !Provenance::KEYS.contains(&other.as_str()))
    {
        return Err(ManifestError::new(
            join(&at, other),
            "unknown key in `provenance`; it has the keys `found_by` and `reason`",
        ));
    }
    let member = |name: &str| match table.get(name) {
        None => Ok(None),
        Some(Value::String(text)) if !text.is_empty() => Ok(Some(text.clone())),
        Some(_) => Err(ManifestError::new(
            join(&at, name),
            format!("`{name}` is a nonempty string"),
        )),
    };
    let provenance = Provenance {
        found_by: member("found_by")?,
        reason: member("reason")?,
    };
    if provenance == Provenance::default() {
        return Err(ManifestError::new(
            at,
            "states neither `found_by` nor `reason`; give one, or remove `provenance`",
        ));
    }
    Ok(Some(provenance))
}

/// Reads the named cases of one document, following its includes.
struct CaseList<'a> {
    files: ManifestFiles<'a>,
    /// The names of the files being read, the matched document's first.
    reading: Vec<String>,
    cases: Vec<DocumentCase>,
    /// Each name taken, with the key of its case.
    names: BTreeMap<String, String>,
    /// Whose case documents the flow reads.
    level: CaseLevel,
}

impl CaseList<'_> {
    /// The case list `value`, named `key`, written in the included file `from` (`None`: the
    /// matched document): an array of named cases and includes, or an include of a file that
    /// holds one.
    fn list(&mut self, value: &Value, key: &str, from: Option<&str>) -> Result<(), ManifestError> {
        if let Some(path) = include(value, key)? {
            return self.included(path, key, from);
        }
        let Value::Array(items) = value else {
            return Err(ManifestError::new(
                key,
                "a list of named cases is an array of cases (TOML's `[[case]]` tables), each with \
                 a `name`, and `{ \"$data-file\" = path }` includes",
            ));
        };
        for (index, item) in items.iter().enumerate() {
            let here = format!("{key}[{index}]");
            if let Some(path) = include(item, &here)? {
                self.included(path, &here, from)?;
                continue;
            }
            let Value::Table(case) = item else {
                return Err(ManifestError::new(
                    here,
                    format!("a named case is a table of {}", self.level.listed(true)),
                ));
            };
            let mut case = case.clone();
            let name = match case.remove("name") {
                Some(Value::String(name)) if !name.is_empty() => name,
                Some(_) => {
                    return Err(ManifestError::new(
                        join(&here, "name"),
                        "a case's name is a nonempty string",
                    ));
                }
                None => {
                    return Err(ManifestError::new(
                        here,
                        "a case in a list of named cases has a `name`",
                    ));
                }
            };
            if let Some(first) = self.names.get(&name) {
                return Err(ManifestError::new(
                    join(&here, "name"),
                    format!(
                        "`{name}` is also the name of the case at {first}; the cases of a \
                         document have distinct names"
                    ),
                ));
            }
            if let Some(other) = case
                .keys()
                .find(|other| !self.level.keys().contains(&other.as_str()))
            {
                let message = if other == "run" {
                    run_refused(case.get("run"))
                } else {
                    format!(
                        "unknown key in a named case; it has the keys {}",
                        self.level.listed(true)
                    )
                };
                return Err(ManifestError::new(join(&here, other), message));
            }
            self.names.insert(name.clone(), here.clone());
            let inputs = super::inputs(&case, &here)?;
            let (expect, rejected) = expect(&mut case, &here, self.level)?;
            self.cases.push(DocumentCase {
                start_sort: start_sort(&case, &inputs, &here)?,
                inputs,
                expect,
                rejected,
                expect_for: expect_for(&mut case, &here, self.level)?,
                provenance: provenance(&mut case, &here)?,
                name: Some(name),
                file: from.map(str::to_owned),
            });
        }
        Ok(())
    }

    /// The cases of the file `path`, included at `key` from the file `from`.
    fn included(&mut self, path: &str, key: &str, from: Option<&str>) -> Result<(), ManifestError> {
        let refused = |message: String| ManifestError::new(key, message);
        let (name, bytes) = self
            .files
            .read(from, path)
            .map_err(|message| refused(format!("`$data-file` `{path}`: {message}")))?;
        if let Some(first) = self.reading.iter().position(|file| *file == name) {
            let cycle = self.reading[first..]
                .iter()
                .chain([&name])
                .map(|file| format!("`{file}`"))
                .collect::<Vec<_>>()
                .join(" includes ");
            return Err(refused(format!(
                "`$data-file` `{path}` includes a file being read: {cycle}"
            )));
        }
        let text = String::from_utf8(bytes)
            .map_err(|_| refused(format!("`$data-file` `{name}` is no UTF-8 text")))?;
        let extension = Path::new(&name)
            .extension()
            .and_then(std::ffi::OsStr::to_str)
            .unwrap_or_default();
        // A JSON document is read as TOML values, the values kink hands the front end: JSON's
        // null and an integer beyond TOML's 64-bit signed range have none, and are refused.
        let document = if extension.eq_ignore_ascii_case("toml") {
            toml::from_str::<Table>(&text)
                .map(Value::Table)
                .map_err(|e| e.to_string())
        } else if extension.eq_ignore_ascii_case("json") {
            serde_json::from_str::<Value>(&text).map_err(|e| e.to_string())
        } else {
            Err("a data file is `.toml` or `.json`, by its extension".to_owned())
        }
        .map_err(|message| refused(format!("`$data-file` `{name}`: {message}")))?;
        let here = format!("{key}$data-file({path})");
        let list = match document {
            Value::Table(mut table) if table.len() == 1 && table.contains_key("case") => {
                table.remove("case").expect("checked")
            }
            list @ Value::Array(_) => list,
            _ => {
                return Err(ManifestError::new(
                    here,
                    "an included file of named cases holds their list: an array, or a table \
                     whose one key is `case`",
                ));
            }
        };
        self.reading.push(name.clone());
        let read = self.list(&list, &here, Some(&name));
        self.reading.pop();
        read
    }
}

/// The path an include (`{ "$data-file" = path }`) at `key` names, or `None` for a value that is
/// no tagged form.
fn include<'v>(value: &'v Value, key: &str) -> Result<Option<&'v str>, ManifestError> {
    let Value::Table(table) = value else {
        return Ok(None);
    };
    if !table.keys().any(|tag| tag.starts_with('$')) {
        return Ok(None);
    }
    let mut entries = table.iter();
    match (entries.next(), entries.next()) {
        (Some((tag, Value::String(path))), None) if tag == "$data-file" => Ok(Some(path)),
        (Some((tag, _)), None) if tag == "$data-file" => {
            Err(ManifestError::new(key, "`$data-file` takes a path string"))
        }
        (Some((tag, _)), None) => Err(ManifestError::new(
            key,
            format!("`{tag}` is no case; a list of named cases includes a file with `$data-file`"),
        )),
        _ => Err(ManifestError::new(
            key,
            "a tagged form is a table with exactly one key",
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::super::{
        ExpectFor, FlowManifest, ManifestError, ManifestFile, Provenance, RejectedStage,
        SpecSection,
    };
    use crate::admit::CaseInputs;
    use crate::digest::{program_digest, program_payload};
    use std::{fs, path::PathBuf};

    /// A fresh corpus of this test process holding `files` (path, text) under `cases/`, whose
    /// manifest matches every `.toml` file directly under `cases/` (`cases/data/` holds the
    /// included files).
    fn corpus(name: &str, files: &[(&str, &str)]) -> PathBuf {
        let dir = std::env::temp_dir()
            .join(format!(
                "kink-flow-case-document-unit-{}",
                std::process::id()
            ))
            .join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(dir.join("cases/data")).unwrap();
        for (path, text) in files {
            fs::write(dir.join("cases").join(path), text).unwrap();
        }
        fs::write(
            dir.join("FLOW.toml"),
            "[spec]\nentry = \"x.k\"\nmain_module = \"X\"\n\n[[program]]\ncases = \"cases/*.toml\"\n",
        )
        .unwrap();
        dir
    }

    fn read(name: &str, files: &[(&str, &str)]) -> Result<FlowManifest, ManifestError> {
        FlowManifest::read(&corpus(name, files).join("FLOW.toml"))
    }

    /// [`read`] under a KRS declaration (`[spec] krs`), whose case documents krs-exec reads too.
    fn read_krs(name: &str, files: &[(&str, &str)]) -> Result<ManifestFile, ManifestError> {
        let dir = corpus(name, files);
        fs::write(
            dir.join("FLOW.toml"),
            "[spec]\nkrs = { package = \"pkg\", definition = \"main\" }\n\n[[program]]\ncases = \"cases/*.toml\"\n",
        )
        .unwrap();
        ManifestFile::read(&dir.join("FLOW.toml"))
    }

    fn stated(found_by: Option<&str>, reason: Option<&str>) -> Option<Provenance> {
        Some(Provenance {
            found_by: found_by.map(str::to_owned),
            reason: reason.map(str::to_owned),
        })
    }

    /// The documents krs-exec's case table reads alike (krs-exec `inputs::tests`,
    /// `a_case_provenance_is_read_as_kink_reads_it`): each accepted with the provenance of its
    /// cases in order, or refused at the key named.
    const ACCEPTED: [&str; 3] = [
        "provenance = { found_by = \"cargo-fuzz\", reason = \"a prefix read twice\" }\n[inputs]\nn = 1\n",
        "[[case]]\nname = \"a\"\nprovenance = { reason = \"from the manual\" }\n[[case]]\nname = \"b\"\n",
        "case = [{ \"$data-file\" = \"data/more.toml\" }]\n",
    ];

    /// A case's `provenance` is read in a document of one case, in a named case and in a case of
    /// an included file, each member optional; a case without one has none.
    #[test]
    fn a_case_states_its_provenance() {
        let more = (
            "data/more.toml",
            "[[case]]\nname = \"c\"\nprovenance = { found_by = \"libafl\" }\ninputs = { n = 3 }\n",
        );
        let manifest = read(
            "provenance-read",
            &[
                ("one.toml", ACCEPTED[0]),
                ("named.toml", ACCEPTED[1]),
                ("included.toml", ACCEPTED[2]),
                more,
            ],
        )
        .unwrap();
        let read = manifest
            .programs
            .iter()
            .map(|program| (program.id.as_str(), program.provenance.clone()))
            .collect::<Vec<_>>();
        assert_eq!(
            read,
            [
                ("cases/included.toml#c", stated(Some("libafl"), None)),
                ("cases/named.toml#a", stated(None, Some("from the manual"))),
                ("cases/named.toml#b", None),
                (
                    "cases/one.toml",
                    stated(Some("cargo-fuzz"), Some("a prefix read twice"))
                ),
            ]
        );
    }

    /// A `provenance` that is no table, states neither member, has another member, a member
    /// that is no nonempty string, or stands at the top of a document of named cases is refused,
    /// naming its position.
    #[test]
    fn a_malformed_provenance_is_refused() {
        let id = "program \"cases/case.toml\"";
        for (document, key, message) in [
            (
                "provenance = \"fuzz\"\n",
                format!("{id}.provenance"),
                "is a table of `found_by` and `reason`",
            ),
            (
                "provenance = {}\n",
                format!("{id}.provenance"),
                "states neither `found_by` nor `reason`",
            ),
            (
                "provenance = { found_by = \"a\", tool = \"b\" }\n",
                format!("{id}.provenance.tool"),
                "unknown key in `provenance`",
            ),
            (
                "provenance = { found_by = 1 }\n",
                format!("{id}.provenance.found_by"),
                "`found_by` is a nonempty string",
            ),
            (
                "provenance = { reason = \"\" }\n",
                format!("{id}.provenance.reason"),
                "`reason` is a nonempty string",
            ),
            (
                "[[case]]\nname = \"a\"\nprovenance = { found_by = [\"a\"] }\n",
                format!("{id}.case[0].provenance.found_by"),
                "`found_by` is a nonempty string",
            ),
            (
                "provenance = { found_by = \"a\" }\n[[case]]\nname = \"a\"\n",
                format!("{id}.provenance"),
                "a document of named cases holds `case` only",
            ),
        ] {
            let error = read("provenance-refused", &[("case.toml", document)]).expect_err(document);
            assert_eq!(error.key, key, "{document}: {error}");
            assert!(error.message.contains(message), "{document}: {error}");
        }
    }

    /// Two cases that differ only in their provenance are one program to every store: the same
    /// program payload and digest (README 5.3), which every result and outcome key holds.
    #[test]
    fn a_case_provenance_is_in_no_program_digest() {
        let program = |name: &str, document: &str| {
            read(name, &[("case.toml", document)])
                .unwrap()
                .programs
                .remove(0)
        };
        let bare = program("provenance-bare", "[inputs]\nn = 1\n");
        let stated = program(
            "provenance-stated",
            "provenance = { found_by = \"cargo-fuzz\", reason = \"why\" }\n[inputs]\nn = 1\n",
        );
        assert_ne!(bare.provenance, stated.provenance);
        assert_eq!(bare.inputs, stated.inputs);
        let inputs = CaseInputs {
            text: None,
            typed: Vec::new(),
            bound: None,
            defaults: Vec::new(),
            texts: Vec::new(),
        };
        assert_eq!(
            program_payload(&bare, &inputs),
            program_payload(&stated, &inputs)
        );
        assert_eq!(
            program_digest(&bare, &inputs),
            program_digest(&stated, &inputs)
        );
    }

    /// The documents of scoped expectations krs-exec's case table reads alike (krs-exec
    /// `inputs::tests::a_case_expect_for_is_read_as_kink_reads_it`): each accepted, or refused at
    /// the key named (relative to the case document's key) with the message given.
    const EXPECT_FOR_ACCEPTED: [&str; 3] = [
        "[expect]\nhalt = \"stuck\"\n[expect_for.X]\nclass = \"refused\"\n[expect_for.Y]\nhalt = \"stopped\"\n",
        "[[case]]\nname = \"a\"\n[case.expect_for.X]\nhalt = \"stuck\"\n[[case]]\nname = \"b\"\n",
        "[expect_for.Y]\nhalt = \"stuck\"\n",
    ];
    const EXPECT_FOR_REFUSED: [(&str, &str, &str); 10] = [
        (
            "[expect]\nrejected = \"parse\"\n",
            "expect.rejected",
            "a program that must be rejected before it runs is stated on a `[[program]]`",
        ),
        (
            "[expect]\nhalt = \"stuck\"\nrejected = \"input\"\n",
            "expect.rejected",
            "a program that must be rejected before it runs is stated on a `[[program]]`",
        ),
        (
            "[expect_for.X]\nrejected = \"parse\"\n",
            "expect_for.X.rejected",
            "a program that must be rejected before it runs is stated on a `[[program]]`",
        ),
        (
            "[[case]]\nname = \"a\"\n[case.expect]\nrejected = \"input\"\n",
            "case[0].expect.rejected",
            "a program that must be rejected before it runs is stated on a `[[program]]`",
        ),
        (
            "expect_for = 1\n",
            "expect_for",
            "`expect_for` is a table of expected ends by definition name",
        ),
        (
            "expect_for = {}\n",
            "expect_for",
            "scopes no expectation to a definition",
        ),
        (
            "expect_for = { X = 1 }\n",
            "expect_for.X",
            "an expectation scoped to a definition is a table",
        ),
        (
            "[expect_for.\"\"]\nhalt = \"stuck\"\n",
            "expect_for.",
            "a definition name is a nonempty string",
        ),
        (
            "[[case]]\nname = \"a\"\nexpect_for = { X = [1] }\n",
            "case[0].expect_for.X",
            "an expectation scoped to a definition is a table",
        ),
        (
            "expect_for = { X = { halt = \"stuck\" } }\n[[case]]\nname = \"a\"\n",
            "expect_for",
            "a document of named cases holds `case` only",
        ),
    ];

    fn scoped(definition: &str, document: &str) -> Option<(String, toml::Table)> {
        Some((definition.to_owned(), toml::from_str(document).unwrap()))
    }

    fn names(names: &[&str]) -> std::collections::BTreeSet<String> {
        names.iter().map(|name| (*name).to_owned()).collect()
    }

    /// A K flow (main module `X`) reads the expectation a case scopes to `X`, beside the case's
    /// `expect`, in a document of one case, a named case and an included file's case; it keeps the
    /// name of every definition a case scopes one to, and reads no other's expectation. A
    /// mistyped `[expect.X]` is a member of `expect`, never a scope.
    #[test]
    fn a_flow_reads_the_expectation_scoped_to_its_main_module() {
        let manifest = read(
            "expect-for-k",
            &[
                ("both.toml", EXPECT_FOR_ACCEPTED[0]),
                ("named.toml", EXPECT_FOR_ACCEPTED[1]),
                ("other.toml", EXPECT_FOR_ACCEPTED[2]),
                (
                    "included.toml",
                    "case = [{ \"$data-file\" = \"data/more.toml\" }]\n",
                ),
                (
                    "data/more.toml",
                    "[[case]]\nname = \"c\"\nexpect_for = { X = { halt = \"stuck\" } }\n",
                ),
                ("mistyped.toml", "[expect.X]\nhalt = \"stuck\"\n"),
            ],
        )
        .unwrap();
        let read = manifest
            .programs
            .iter()
            .map(|program| {
                (
                    program.id.as_str(),
                    program.expect.clone(),
                    program.expect_for.clone(),
                )
            })
            .collect::<Vec<_>>();
        let stuck = || scoped("X", "halt = \"stuck\"");
        assert_eq!(
            read,
            [
                (
                    "cases/both.toml",
                    Some(toml::from_str("halt = \"stuck\"").unwrap()),
                    ExpectFor {
                        scoped: scoped("X", "class = \"refused\""),
                        definitions: names(&["X", "Y"]),
                    }
                ),
                (
                    "cases/included.toml#c",
                    None,
                    ExpectFor {
                        scoped: stuck(),
                        definitions: names(&["X"]),
                    }
                ),
                (
                    "cases/mistyped.toml",
                    Some(toml::from_str("[X]\nhalt = \"stuck\"").unwrap()),
                    ExpectFor::default()
                ),
                (
                    "cases/named.toml#a",
                    None,
                    ExpectFor {
                        scoped: stuck(),
                        definitions: names(&["X"]),
                    }
                ),
                ("cases/named.toml#b", None, ExpectFor::default()),
                (
                    "cases/other.toml",
                    None,
                    ExpectFor {
                        scoped: None,
                        definitions: names(&["Y"]),
                    }
                ),
            ]
        );
        assert_eq!(manifest.expect_scope, "X");
    }

    /// A KRS flow selects by its facet (`definition`), not by `PACKAGE:FACET` nor by the main
    /// module of the K its front end binds.
    #[test]
    fn a_krs_flow_reads_the_expectation_scoped_to_its_facet() {
        let dir = corpus(
            "expect-for-krs",
            &[(
                "case.toml",
                "[expect_for.main]\nhalt = \"stuck\"\n[expect_for.\"pkg:main\"]\nhalt = \"stopped\"\n\
                 [expect_for.EMITTED]\nclass = \"refused\"\n",
            )],
        );
        fs::write(
            dir.join("FLOW.toml"),
            "[spec]\nkrs = { package = \"pkg\", definition = \"main\" }\n\n[[program]]\ncases = \"cases/*.toml\"\n",
        )
        .unwrap();
        let file = ManifestFile::read(&dir.join("FLOW.toml")).unwrap();
        assert_eq!(file.spec.expect_scope(), "main");
        let bound = file
            .bind(Some(SpecSection {
                entry: "emitted.k".to_owned(),
                main_module: "EMITTED".to_owned(),
                syntax_module: None,
                include_dirs: Vec::new(),
                md_selector: "k".to_owned(),
                assume_joined: Vec::new(),
            }))
            .unwrap();
        assert_eq!(bound.expect_scope, "main");
        assert_eq!(bound.definition.as_deref(), Some("pkg:main"));
        assert_eq!(
            bound.programs[0].expect_for,
            ExpectFor {
                scoped: scoped("main", "halt = \"stuck\""),
                definitions: names(&["EMITTED", "main", "pkg:main"]),
            }
        );
    }

    /// An `expect_for` that is no table, scopes nothing, has an empty definition name or a value
    /// that is no table, or stands at the top of a document of named cases is refused, naming its
    /// position, and so is `rejected` in `expect` or a scoped expectation (PJ-32: it is stated on
    /// a `[[program]]` or `files` entry), in a KRS flow, whose case documents krs-exec reads by
    /// the same rule; a K flow refuses each but `rejected` in `expect` alike.
    #[test]
    fn a_malformed_expect_for_is_refused() {
        let id = "program \"cases/case.toml\"";
        for (document, key, message) in EXPECT_FOR_REFUSED {
            let error =
                read_krs("expect-for-refused", &[("case.toml", document)]).expect_err(document);
            assert_eq!(error.key, format!("{id}.{key}"), "{document}: {error}");
            assert!(error.message.contains(message), "{document}: {error}");
            if key.ends_with("expect.rejected") {
                continue;
            }
            let error = read("expect-for-refused", &[("case.toml", document)]).expect_err(document);
            assert_eq!(error.key, format!("{id}.{key}"), "{document}: {error}");
            if key.ends_with(".rejected") {
                assert!(
                    error.message.contains("states it in `expect`"),
                    "{document}: {error}"
                );
            } else {
                assert!(error.message.contains(message), "{document}: {error}");
            }
        }
    }

    /// A case of a K flow binds K texts, which are parsed (PJ-36): it may give `start_sort`, the
    /// sort its program text (`PGM`) is read at, and `expect = { rejected = STAGE }`, in a
    /// document of one case, a named case and an included file's case; both become the program's
    /// own (`start_sort`, `rejected`), and the case written as a document of one case states them.
    #[test]
    fn a_k_case_states_its_start_sort_and_its_rejection() {
        let manifest = read(
            "k-case-keys",
            &[
                (
                    "one.toml",
                    "start_sort = \"Exp\"\nexpect = { rejected = \"parse\" }\n[inputs]\nPGM = \"1 +\"\n",
                ),
                (
                    "named.toml",
                    "[[case]]\nname = \"a\"\nexpect = { rejected = \"input\" }\n\
                     [[case]]\nname = \"b\"\nstart_sort = \"Int\"\ninputs = { PGM = \"1\", N = \"2\" }\n\
                     [[case]]\n\"$data-file\" = \"data/more.toml\"\n",
                ),
                (
                    "data/more.toml",
                    "[[case]]\nname = \"c\"\nstart_sort = \"Exp\"\nexpect = { rejected = \"parse\" }\n\
                     inputs = { PGM = { \"$file\" = \"bad.txt\" } }\n",
                ),
            ],
        )
        .unwrap();
        let read = manifest
            .programs
            .iter()
            .map(|program| {
                (
                    program.id.as_str(),
                    program.start_sort.as_deref(),
                    program.rejected.map(RejectedStage::as_str),
                    program.expect.is_some(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            read,
            [
                ("cases/named.toml#a", None, Some("input"), false),
                ("cases/named.toml#b", Some("Int"), None, false),
                ("cases/named.toml#c", Some("Exp"), Some("parse"), false),
                ("cases/one.toml", Some("Exp"), Some("parse"), false),
            ]
        );
        let dir = std::env::temp_dir()
            .join(format!(
                "kink-flow-case-document-unit-{}",
                std::process::id()
            ))
            .join("k-case-keys");
        let cases = manifest
            .document_cases(&dir.join("cases/one.toml"))
            .unwrap();
        let (program, table) = &cases[0];
        assert_eq!(program.rejected, Some(RejectedStage::Parse));
        let written: toml::Table = toml::from_str(
            "start_sort = \"Exp\"\nexpect = { rejected = \"parse\" }\n[inputs]\nPGM = \"1 +\"\n",
        )
        .unwrap();
        assert_eq!(table, &written);
    }

    /// At the K level, a `start_sort` without `PGM` in `inputs`, one that is no string, and an
    /// `expect` that states a rejection beside another key or at a stage that is none are refused,
    /// naming the position; a KRS flow refuses `start_sort` and `rejected` as krs-exec does, with
    /// the keys of a krs case.
    #[test]
    fn a_k_case_refuses_a_start_sort_without_a_program_text() {
        let id = "program \"cases/case.toml\"";
        for (document, key, message) in [
            (
                "start_sort = \"Exp\"\n[inputs]\nN = \"1\"\n",
                "start_sort",
                "applies to the program text, `PGM` in `inputs`",
            ),
            (
                "start_sort = 1\n[inputs]\nPGM = \"1\"\n",
                "start_sort",
                "expected a string",
            ),
            (
                "[expect]\nrejected = \"parse\"\nhalt = \"stuck\"\n",
                "expect.halt",
                "with no expected end beside it",
            ),
            (
                "expect = { rejected = \"end\" }\n",
                "expect.rejected",
                "with no expected end beside it",
            ),
            (
                "[[case]]\nname = \"a\"\nstart_sort = \"Exp\"\n",
                "case[0].start_sort",
                "applies to the program text",
            ),
            (
                "[[case]]\nname = \"a\"\nsort = \"Exp\"\n",
                "case[0].sort",
                "it has the keys `name`, `inputs`, `start_sort`, `expect`, `expect_for` and \
                 `provenance`",
            ),
            (
                "sort = \"Exp\"\n",
                "sort",
                "a case has the keys `inputs`, `start_sort`, `expect`, `expect_for` and \
                 `provenance`",
            ),
        ] {
            let error = read("k-case-refused", &[("case.toml", document)]).expect_err(document);
            assert_eq!(error.key, format!("{id}.{key}"), "{document}: {error}");
            assert!(error.message.contains(message), "{document}: {error}");
        }
        for (document, key, message) in [
            (
                "start_sort = \"Exp\"\n[inputs]\nPGM = \"1\"\n",
                "start_sort",
                "unknown key in a case document; a case has the keys `inputs`, `expect`, \
                 `expect_for` and `provenance`",
            ),
            (
                "[[case]]\nname = \"a\"\nstart_sort = \"Exp\"\n",
                "case[0].start_sort",
                "unknown key in a named case; it has the keys `name`, `inputs`, `expect`, \
                 `expect_for` and `provenance`",
            ),
            (
                "expect = { rejected = \"parse\" }\n",
                "expect.rejected",
                "a case document's typed inputs are never parsed",
            ),
        ] {
            let error =
                read_krs("krs-case-refused", &[("case.toml", document)]).expect_err(document);
            assert_eq!(error.key, format!("{id}.{key}"), "{document}: {error}");
            assert!(error.message.contains(message), "{document}: {error}");
        }
    }

    /// Two cases that differ only in their scoped expectations are one program to every store:
    /// the same program payload and digest.
    #[test]
    fn a_scoped_expectation_is_in_no_program_digest() {
        let program = |name: &str, document: &str| {
            read(name, &[("case.toml", document)])
                .unwrap()
                .programs
                .remove(0)
        };
        let bare = program("expect-for-bare", "[inputs]\nn = 1\n");
        let scoped = program(
            "expect-for-scoped",
            "[inputs]\nn = 1\n[expect_for.X]\nhalt = \"stuck\"\n[expect_for.Y]\nhalt = \"stuck\"\n",
        );
        assert_ne!(bare.expect_for, scoped.expect_for);
        let inputs = CaseInputs {
            text: None,
            typed: Vec::new(),
            bound: None,
            defaults: Vec::new(),
            texts: Vec::new(),
        };
        assert_eq!(
            program_payload(&bare, &inputs),
            program_payload(&scoped, &inputs)
        );
        assert_eq!(
            program_digest(&bare, &inputs),
            program_digest(&scoped, &inputs)
        );
    }
}
