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

use super::{CaseRoot, ManifestError, Provenance, join, program_key};
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

/// The keys of a case, besides a named case's `name`.
const CASE_KEYS: [&str; 4] = ["inputs", "expect", "expect_for", "provenance"];

/// The one case of a document whose top is `document`, named `key`.
fn one_case(mut document: Table, key: &str) -> Result<DocumentCase, ManifestError> {
    if let Some(other) = document
        .keys()
        .find(|other| !CASE_KEYS.contains(&other.as_str()))
    {
        let message = match other.as_str() {
            "run" => run_refused(document.get("run")),
            "name" => {
                "a document of one case names none; named cases are listed under `case`".to_owned()
            }
            _ => "unknown key in a case document; a case has the keys `inputs`, `expect`, \
                  `expect_for` and `provenance`"
                .to_owned(),
        };
        return Err(ManifestError::new(join(key, other), message));
    }
    Ok(DocumentCase {
        name: None,
        inputs: super::inputs(&document, key)?,
        expect: expect(&mut document, key)?,
        expect_for: expect_for(&mut document, key)?,
        provenance: provenance(&mut document, key)?,
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

/// `expect_for` of a case named `key`: a nonempty table of tables by nonempty definition name,
/// when given (module documentation); empty when absent.
fn expect_for(case: &mut Table, key: &str) -> Result<BTreeMap<String, Table>, ManifestError> {
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
            Value::Table(expect) => Ok((definition, expect)),
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
                    "a named case is a table of `name`, `inputs`, `expect`, `expect_for` and \
                     `provenance`",
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
                .find(|other| !CASE_KEYS.contains(&other.as_str()))
            {
                let message = if other == "run" {
                    run_refused(case.get("run"))
                } else {
                    "unknown key in a named case; it has the keys `name`, `inputs`, `expect`, \
                     `expect_for` and `provenance`"
                        .to_owned()
                };
                return Err(ManifestError::new(join(&here, other), message));
            }
            self.names.insert(name.clone(), here.clone());
            self.cases.push(DocumentCase {
                inputs: super::inputs(&case, &here)?,
                expect: expect(&mut case, &here)?,
                expect_for: expect_for(&mut case, &here)?,
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
        ExpectFor, FlowManifest, ManifestError, ManifestFile, Provenance, SpecSection,
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
    const EXPECT_FOR_REFUSED: [(&str, &str, &str); 6] = [
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
    /// position.
    #[test]
    fn a_malformed_expect_for_is_refused() {
        let id = "program \"cases/case.toml\"";
        for (document, key, message) in EXPECT_FOR_REFUSED {
            let error = read("expect-for-refused", &[("case.toml", document)]).expect_err(document);
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
