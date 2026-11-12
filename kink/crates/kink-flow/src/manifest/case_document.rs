//! A case document a `cases` pattern matched: one case, or named cases (the krs case document,
//! read here with kink's containment rule).
//!
//! A document of one case holds `inputs` and `expect` at its top. A document of named cases holds
//! `case`, the list of its cases: an array (TOML's `[[case]]` tables) of named cases, each a table
//! of `name`, `inputs` and `expect`, and of includes, `{ "$data-file" = "path" }`, each naming a
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

use super::{CaseRoot, ManifestError, join, program_key};
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

/// One case of a case document.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct DocumentCase {
    /// Its name, in a document of named cases; `None` for the one case of a document.
    pub(super) name: Option<String>,
    /// `inputs`: typed inputs by nonempty input name, kept as written.
    pub(super) inputs: Table,
    /// `expect`: the end the case expects, kept as written.
    pub(super) expect: Option<Table>,
    /// The name of the included file the case is written in, as [`InputFiles::read`] gives it
    /// (its path relative to the manifest's directory, links resolved); `None` for a case of the
    /// matched document itself.
    pub(super) file: Option<String>,
}

/// The cases of the case document `id` (a path relative to the canonical case root `root`),
/// which must resolve, links included, to a file inside `root`, in document order.
pub(super) fn case_document(root: &CaseRoot, id: &str) -> Result<Vec<DocumentCase>, ManifestError> {
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
        return one_case(document, &key).map(|case| vec![case]);
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

/// The one case of a document whose top is `document`, named `key`.
fn one_case(mut document: Table, key: &str) -> Result<DocumentCase, ManifestError> {
    if let Some(other) = document
        .keys()
        .find(|other| !matches!(other.as_str(), "inputs" | "expect"))
    {
        let message = match other.as_str() {
            "run" => run_refused(document.get("run")),
            "name" => {
                "a document of one case names none; named cases are listed under `case`".to_owned()
            }
            _ => "unknown key in a case document; a case has the keys `inputs` and `expect`"
                .to_owned(),
        };
        return Err(ManifestError::new(join(key, other), message));
    }
    Ok(DocumentCase {
        name: None,
        inputs: super::inputs(&document, key)?,
        expect: expect(&mut document, key)?,
        file: None,
    })
}

/// `expect` of a case named `key`: a table, when given.
fn expect(case: &mut Table, key: &str) -> Result<Option<Table>, ManifestError> {
    match case.remove("expect") {
        None => Ok(None),
        Some(Value::Table(expect)) => Ok(Some(expect)),
        Some(_) => Err(ManifestError::new(
            join(key, "expect"),
            "expected a table of the expected end: `halt`, `rule`, `cells` and `compare`",
        )),
    }
}

/// Reads the named cases of one document, following its includes.
struct CaseList<'a> {
    files: ManifestFiles<'a>,
    /// The names of the files being read, the matched document's first.
    reading: Vec<String>,
    cases: Vec<DocumentCase>,
    /// Each name taken, with the key of its case.
    names: BTreeMap<String, String>,
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
                    "a named case is a table of `name`, `inputs` and `expect`",
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
                .find(|other| !matches!(other.as_str(), "inputs" | "expect"))
            {
                let message = if other == "run" {
                    run_refused(case.get("run"))
                } else {
                    "unknown key in a named case; it has the keys `name`, `inputs` and `expect`"
                        .to_owned()
                };
                return Err(ManifestError::new(join(&here, other), message));
            }
            self.names.insert(name.clone(), here.clone());
            self.cases.push(DocumentCase {
                inputs: super::inputs(&case, &here)?,
                expect: expect(&mut case, &here)?,
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
