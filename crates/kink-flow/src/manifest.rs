//! `FLOW.toml`, the corpus manifest an LLM writes (flow README section 5.2).
//!
//! Decoding is strict: an unknown key, a value of the wrong type, a duplicate program id,
//! a program with both or neither of `file` and `text`, or a path that leaves the
//! manifest's directory is an error naming the key or the program id, so that a typo is
//! never silently ignored.

use kink_corpus::ProgramSource;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    path::{Component, Path, PathBuf},
};
use toml::{Table, Value};

/// Default wall-clock budget of one program run, in milliseconds.
pub const DEFAULT_TIME_MS: u64 = 10_000;
/// Default rewrite-depth bound of one program run. Every run is bounded (NEXT-PLAN 2.2
/// forbids unbounded runs), so the bound is never absent.
pub const DEFAULT_MAX_DEPTH: u64 = 100_000;
/// Default include directories: the manifest's directory.
pub const DEFAULT_INCLUDE_DIRS: [&str; 1] = ["."];
/// Default Markdown code-block selector.
pub const DEFAULT_MD_SELECTOR: &str = "k";

/// A decoded corpus manifest. Every path is relative to [`FlowManifest::directory`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlowManifest {
    /// The directory holding the manifest; the root that every path stays inside.
    pub directory: PathBuf,
    pub spec: SpecSection,
    pub budget: Budget,
    pub programs: Vec<Program>,
}

/// `[spec]`: how to load the K specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecSection {
    pub entry: String,
    pub main_module: String,
    pub syntax_module: Option<String>,
    pub include_dirs: Vec<String>,
    pub md_selector: String,
}

/// `[budget]`: the bounds of every program run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Budget {
    pub time_ms: u64,
    pub max_depth: u64,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            time_ms: DEFAULT_TIME_MS,
            max_depth: DEFAULT_MAX_DEPTH,
        }
    }
}

/// One `[[program]]`: a concrete corpus program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    pub id: String,
    /// `file` (relative to the manifest's directory) or inline `text`.
    pub source: ProgramSource,
    pub start_sort: Option<String>,
    /// Configuration variables, name (without `$`) to text, sorted by name.
    pub variables: Vec<(String, String)>,
}

/// A manifest that cannot be read or decoded. `key` names the offending key (for example
/// `spec.entry`) or program (`program "add"`); it is empty for a TOML syntax error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ManifestError {
    pub key: String,
    pub message: String,
}

impl ManifestError {
    pub(crate) fn new(key: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.key.is_empty() {
            f.write_str(&self.message)
        } else {
            write!(f, "{}: {}", self.key, self.message)
        }
    }
}

impl std::error::Error for ManifestError {}

impl FlowManifest {
    /// Read and decode the manifest at `path`; its directory becomes the root.
    pub fn read(path: &Path) -> Result<Self, ManifestError> {
        let text = fs::read_to_string(path)
            .map_err(|e| ManifestError::new("", format!("cannot read the manifest: {e}")))?;
        let directory = match path.parent() {
            Some(parent) if !parent.as_os_str().is_empty() => parent.to_path_buf(),
            _ => PathBuf::from("."),
        };
        Self::decode(&text, &directory)
    }

    /// Decode manifest `text` whose paths are relative to `directory`.
    pub fn decode(text: &str, directory: &Path) -> Result<Self, ManifestError> {
        let top: Table = toml::from_str(text)
            .map_err(|e| ManifestError::new("", format!("invalid TOML: {e}")))?;
        known_keys(&top, "", &["spec", "budget", "program"])?;
        let spec = spec(top.get("spec").ok_or_else(|| missing("spec"))?)?;
        let budget = match top.get("budget") {
            None => Budget::default(),
            Some(value) => budget(value)?,
        };
        let programs = match top.get("program") {
            None => Vec::new(),
            Some(Value::Array(entries)) => entries
                .iter()
                .enumerate()
                .map(|(index, entry)| program(index, entry))
                .collect::<Result<Vec<_>, _>>()?,
            Some(_) => return Err(ManifestError::new("program", "expected [[program]] tables")),
        };
        let mut ids = BTreeSet::new();
        for program in &programs {
            if !ids.insert(program.id.as_str()) {
                return Err(ManifestError::new(
                    program_key(&program.id),
                    "duplicate program id",
                ));
            }
        }
        Ok(Self {
            directory: directory.to_path_buf(),
            spec,
            budget,
            programs,
        })
    }
}

fn missing(key: &str) -> ManifestError {
    ManifestError::new(key, "missing required key")
}

fn program_key(id: &str) -> String {
    format!("program {id:?}")
}

fn join(prefix: &str, key: &str) -> String {
    if prefix.is_empty() {
        key.to_owned()
    } else {
        format!("{prefix}.{key}")
    }
}

fn table<'a>(value: &'a Value, key: &str) -> Result<&'a Table, ManifestError> {
    value
        .as_table()
        .ok_or_else(|| ManifestError::new(key, "expected a table"))
}

fn known_keys(table: &Table, prefix: &str, known: &[&str]) -> Result<(), ManifestError> {
    match table.keys().find(|key| !known.contains(&key.as_str())) {
        Some(key) => Err(ManifestError::new(join(prefix, key), "unknown key")),
        None => Ok(()),
    }
}

fn string(value: &Value, key: &str) -> Result<String, ManifestError> {
    match value.as_str() {
        Some(text) if !text.is_empty() => Ok(text.to_owned()),
        Some(_) => Err(ManifestError::new(key, "must not be empty")),
        None => Err(ManifestError::new(key, "expected a string")),
    }
}

fn optional_string(
    table: &Table,
    prefix: &str,
    name: &str,
) -> Result<Option<String>, ManifestError> {
    table
        .get(name)
        .map(|value| string(value, &join(prefix, name)))
        .transpose()
}

fn required_string(table: &Table, prefix: &str, name: &str) -> Result<String, ManifestError> {
    let key = join(prefix, name);
    string(table.get(name).ok_or_else(|| missing(&key))?, &key)
}

/// A relative path that stays inside the manifest's directory, by kink-corpus's resolver
/// rule (`resolver::relative_path`): only normal, `.` and `..` components, and no `..`
/// above the root. Links are resolved later, when the file is read, by the same
/// containment check the resolver makes.
fn relative_path(value: &Value, key: &str) -> Result<String, ManifestError> {
    let text = string(value, key)?;
    let mut depth = 0usize;
    for component in Path::new(&text).components() {
        match component {
            Component::Normal(_) => depth += 1,
            Component::CurDir => {}
            Component::ParentDir if depth > 0 => depth -= 1,
            _ => {
                return Err(ManifestError::new(
                    key,
                    format!("path {text:?} leaves the manifest's directory"),
                ));
            }
        }
    }
    Ok(text)
}

fn positive(table: &Table, prefix: &str, name: &str, default: u64) -> Result<u64, ManifestError> {
    let key = join(prefix, name);
    match table.get(name) {
        None => Ok(default),
        Some(Value::Integer(value)) if *value > 0 => Ok(u64::try_from(*value).expect("positive")),
        Some(Value::Integer(_)) => Err(ManifestError::new(key, "must be positive")),
        Some(_) => Err(ManifestError::new(key, "expected an integer")),
    }
}

fn spec(value: &Value) -> Result<SpecSection, ManifestError> {
    let spec = table(value, "spec")?;
    known_keys(
        spec,
        "spec",
        &[
            "entry",
            "main_module",
            "syntax_module",
            "include_dirs",
            "md_selector",
        ],
    )?;
    let entry = relative_path(
        spec.get("entry").ok_or_else(|| missing("spec.entry"))?,
        "spec.entry",
    )?;
    let include_dirs = match spec.get("include_dirs") {
        None => DEFAULT_INCLUDE_DIRS
            .iter()
            .map(|d| (*d).to_owned())
            .collect(),
        Some(Value::Array(dirs)) => dirs
            .iter()
            .enumerate()
            .map(|(i, dir)| relative_path(dir, &format!("spec.include_dirs[{i}]")))
            .collect::<Result<Vec<_>, _>>()?,
        Some(_) => {
            return Err(ManifestError::new(
                "spec.include_dirs",
                "expected an array of strings",
            ));
        }
    };
    Ok(SpecSection {
        entry,
        main_module: required_string(spec, "spec", "main_module")?,
        syntax_module: optional_string(spec, "spec", "syntax_module")?,
        include_dirs,
        md_selector: optional_string(spec, "spec", "md_selector")?
            .unwrap_or_else(|| DEFAULT_MD_SELECTOR.to_owned()),
    })
}

fn budget(value: &Value) -> Result<Budget, ManifestError> {
    let budget = table(value, "budget")?;
    known_keys(budget, "budget", &["time_ms", "max_depth"])?;
    Ok(Budget {
        time_ms: positive(budget, "budget", "time_ms", DEFAULT_TIME_MS)?,
        max_depth: positive(budget, "budget", "max_depth", DEFAULT_MAX_DEPTH)?,
    })
}

fn program(index: usize, value: &Value) -> Result<Program, ManifestError> {
    let position = format!("program[{index}]");
    let entry = table(value, &position)?;
    let id = required_string(entry, &position, "id")?;
    let key = program_key(&id);
    known_keys(
        entry,
        &key,
        &["id", "file", "text", "start_sort", "variables"],
    )?;
    let source = match (entry.get("file"), entry.get("text")) {
        (Some(file), None) => ProgramSource::File(relative_path(file, &join(&key, "file"))?),
        (None, Some(Value::String(text))) => ProgramSource::Text(text.clone()),
        (None, Some(_)) => {
            return Err(ManifestError::new(join(&key, "text"), "expected a string"));
        }
        (Some(_), Some(_)) => {
            return Err(ManifestError::new(
                key,
                "has both file and text; give exactly one",
            ));
        }
        (None, None) => {
            return Err(ManifestError::new(
                key,
                "has neither file nor text; give exactly one",
            ));
        }
    };
    let variables = match entry.get("variables") {
        None => Vec::new(),
        Some(Value::Table(variables)) => variables
            .iter()
            .map(|(name, text)| {
                let variable_key = join(&join(&key, "variables"), name);
                if name.is_empty() {
                    return Err(ManifestError::new(variable_key, "empty variable name"));
                }
                match text {
                    Value::String(text) => Ok((name.clone(), text.clone())),
                    _ => Err(ManifestError::new(variable_key, "expected a string")),
                }
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?
            .into_iter()
            .collect(),
        Some(_) => {
            return Err(ManifestError::new(
                join(&key, "variables"),
                "expected a table of strings",
            ));
        }
    };
    Ok(Program {
        id,
        source,
        start_sort: optional_string(entry, &key, "start_sort")?,
        variables,
    })
}
