//! `FLOW.toml`, the corpus manifest an LLM writes (flow README section 5.2).
//!
//! Decoding is strict: an unknown key, a value of the wrong type, a duplicate program id,
//! a program with both `file` and `text`, a `start_sort` without a program text, or a path that
//! leaves the manifest's directory is an error naming the key or the program id, so that a typo
//! is never silently ignored.
//!
//! One schema serves both front ends. `[spec]` declares the specification in one of two ways
//! ([`SpecDecl`]): a K specification (`entry`, `main_module`, ...), which kink-flow loads as
//! written, or a KRS package's emitted K (`krs = { definition = "main" }`), which the krs front
//! end binds to the K it emitted for the package it selects. [`ManifestFile`] is the decoded file
//! before that binding; [`ManifestFile::bind`] gives the [`FlowManifest`] every command runs on,
//! so every other key decodes once, for both front ends.

use crate::admit::InputDecoder;
use kink_corpus::ProgramSource;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    path::{Component, Path, PathBuf},
    sync::Arc,
};
use toml::{Table, Value};

/// Default wall-clock budget of one program run, in milliseconds.
pub const DEFAULT_TIME_MS: u64 = 10_000;
/// Default rewrite-depth bound of one program run. Every run is bounded (NEXT-PLAN 2.2
/// forbids unbounded runs), so the bound is never absent.
pub const DEFAULT_MAX_DEPTH: u64 = 100_000;
/// The fixed floor of a calibrated work budget (`[budget] work_factor`): a mutant's result run of
/// a program whose baseline run visited `W` states may visit `work_factor * W + WORK_FLOOR`
/// (kink-campaign `WorkBudget::Calibrated`; re-pin lane 1, L1-1).
pub const WORK_FLOOR: u64 = 10_000;
/// Default include directories: the manifest's directory.
pub const DEFAULT_INCLUDE_DIRS: [&str; 1] = ["."];
/// Default Markdown code-block selector.
pub const DEFAULT_MD_SELECTOR: &str = "k";

/// A decoded corpus manifest. Every path is relative to [`FlowManifest::directory`].
#[derive(Clone, Debug, PartialEq)]
pub struct FlowManifest {
    /// The directory holding the manifest; the root that every path stays inside.
    pub directory: PathBuf,
    pub spec: SpecSection,
    pub budget: Budget,
    pub programs: Vec<Program>,
    /// `[result]`: the cells the programs' second slot compares, when the manifest narrows them;
    /// `None` compares every cell the specification does not declare unobservable.
    pub result: Option<ResultSection>,
    /// The front end's reading of typed inputs (a program's `inputs`), which the front end that
    /// knows the inputs' declared types sets ([`Self::with_input_decoder`]). A decoded `FLOW.toml`
    /// has none: kink reads K text only, and admission refuses a program with `inputs` without
    /// a decoder (`typed-inputs`).
    pub input_decoder: Decoder,
}

/// A front end's [`InputDecoder`], or none. Two manifests' decoders are equal when both are
/// absent or both are the same decoder value.
#[derive(Clone, Default)]
pub struct Decoder(pub Option<Arc<dyn InputDecoder + Send + Sync>>);

impl Decoder {
    /// The decoder, when a front end set one.
    #[must_use]
    pub fn get(&self) -> Option<&(dyn InputDecoder + Send + Sync)> {
        self.0.as_deref()
    }
}

impl fmt::Debug for Decoder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(if self.0.is_some() {
            "Decoder(Some(..))"
        } else {
            "Decoder(None)"
        })
    }
}

impl PartialEq for Decoder {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            _ => false,
        }
    }
}

impl Eq for Decoder {}

/// `[spec]`: how to load the K specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecSection {
    pub entry: String,
    pub main_module: String,
    pub syntax_module: Option<String>,
    pub include_dirs: Vec<String>,
    pub md_selector: String,
    /// `assume_joined`: the findings of the definition's full critical-pair check the author
    /// names as premises (fz26 KINK-BASELINE-FINDINGS), each by the name k-rust-backend's
    /// `data_term::names` gives it (the name `results` prints and k-rust-fuzz's
    /// `definition-findings` and `assume-joined` use), sorted and without repeats. Empty by
    /// default: a definition with a finding then has no data, and every mutation is `unknown`
    /// (`baseline-findings`).
    pub assume_joined: Vec<String>,
}

/// `[result]`: what the programs' second slot compares.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResultSection {
    /// `cells`: the K names of the cells compared (`regs` for `<regs>`), as written; nonempty,
    /// each nonempty, without repeats. Every other cell is left out, except the cells that
    /// enclose one of these; an unobservable cell inside one of these is left out too.
    pub cells: Vec<String>,
}

/// `[budget]`: the bounds of every program run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Budget {
    pub time_ms: u64,
    pub max_depth: u64,
    /// `work_factor`: the work budget of a mutant's run of a program, as a multiple of the
    /// states the program's baseline run visited, plus [`WORK_FLOOR`] (re-pin lane 1, L1-1).
    /// Absent: no work budget (a mutant's run is bounded by `time_ms` and `max_depth` only). A
    /// work-bound run is never complete, so its program is `unknown` for that mutant, never a
    /// kill; the budget never applies to a baseline run.
    pub work_factor: Option<u64>,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            time_ms: DEFAULT_TIME_MS,
            max_depth: DEFAULT_MAX_DEPTH,
            work_factor: None,
        }
    }
}

impl Budget {
    /// The campaign work budget of the mutants' runs.
    #[must_use]
    pub const fn work(self) -> kink_campaign::WorkBudget {
        match self.work_factor {
            None => kink_campaign::WorkBudget::Unbounded,
            Some(factor) => kink_campaign::WorkBudget::Calibrated {
                factor,
                floor: WORK_FLOOR,
            },
        }
    }
}

/// One `[[program]]`: a concrete corpus case, an assignment of a value to each configuration
/// variable of the definition.
#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    pub id: String,
    /// The program text bound to `$PGM`: `file` (relative to the manifest's directory) or inline
    /// `text`; `None` for a case of a definition without `$PGM`, which binds every variable by
    /// name.
    pub source: Option<ProgramSource>,
    /// The sort the program text is read at; only with a program text.
    pub start_sort: Option<String>,
    /// Configuration variables, name (without `$`) to K text, sorted by name.
    pub variables: Vec<(String, String)>,
    /// `inputs`: typed inputs by input name, each a document of the front end's encoding, kept
    /// as written; kink-flow never reads them itself. Only a front end's [`InputDecoder`] reads
    /// them (`FlowManifest::input_decoder`); without one admission refuses the program.
    pub inputs: Table,
}

/// A manifest that cannot be read or decoded. `key` names the offending key (for example
/// `spec.entry`) or program (`program "add"`); it is empty for a TOML syntax error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ManifestError {
    pub key: String,
    pub message: String,
}

impl ManifestError {
    /// An error naming `key` (empty for an error of the whole file).
    pub fn new(key: impl Into<String>, message: impl Into<String>) -> Self {
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

/// A decoded `FLOW.toml` before its specification is bound ([`Self::bind`]). Every path is
/// relative to [`Self::directory`].
#[derive(Clone, Debug, PartialEq)]
pub struct ManifestFile {
    /// The directory holding the manifest; the root that every path stays inside.
    pub directory: PathBuf,
    pub spec: SpecDecl,
    pub budget: Budget,
    pub programs: Vec<Program>,
    /// `[result]`, as [`FlowManifest::result`].
    pub result: Option<ResultSection>,
}

/// How a manifest's `[spec]` declares its specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpecDecl {
    /// `[spec] entry = ...`: a K specification, loaded as declared.
    K(SpecSection),
    /// `[spec] krs = { definition = ... }`: the K a KRS package emits, which the krs front end
    /// binds.
    Krs(KrsSpec),
}

/// `[spec] krs = { definition = "..." }` with the keys a KRS corpus may give beside it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KrsSpec {
    /// The definition facet of the package the corpus is for (`krs --definition`).
    pub definition: String,
    /// `assume_joined`, as [`SpecSection::assume_joined`]: sorted, without repeats.
    pub assume_joined: Vec<String>,
}

/// The keys of `[spec]` that say how K is loaded, which a KRS declaration leaves to its front end.
const K_SPEC_KEYS: [&str; 5] = [
    "entry",
    "main_module",
    "syntax_module",
    "include_dirs",
    "md_selector",
];

impl ManifestFile {
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
        known_keys(&top, "", &["spec", "budget", "result", "program"])?;
        let spec = spec(top.get("spec").ok_or_else(|| missing("spec"))?)?;
        let budget = match top.get("budget") {
            None => Budget::default(),
            Some(value) => budget(value)?,
        };
        let result = top.get("result").map(result).transpose()?;
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
            result,
        })
    }

    /// The manifest with its specification bound. A KRS declaration takes `spec`, the K its front
    /// end emitted for the package (`spec`'s `assume_joined` is replaced by the declaration's: the
    /// front end says how the K is loaded, the corpus's author which findings are premises), and
    /// is refused without one. A K declaration is the specification, so `spec` must be absent.
    /// Every other key is carried over as decoded.
    pub fn bind(self, spec: Option<SpecSection>) -> Result<FlowManifest, ManifestError> {
        let spec = match (self.spec, spec) {
            (SpecDecl::K(declared), None) => declared,
            (SpecDecl::K(_), Some(_)) => {
                return Err(ManifestError::new(
                    "spec.entry",
                    "a K corpus: its [spec] declares the specification, so no front end binds \
                     another; run `kink-flow <command>` on FLOW.toml",
                ));
            }
            (SpecDecl::Krs(_), None) => {
                return Err(ManifestError::new(
                    "spec.krs",
                    "a KRS corpus: run `krs kink <command>` in the package",
                ));
            }
            (SpecDecl::Krs(declared), Some(bound)) => {
                bound_spec(&bound)?;
                SpecSection {
                    assume_joined: declared.assume_joined,
                    ..bound
                }
            }
        };
        Ok(FlowManifest {
            directory: self.directory,
            spec,
            budget: self.budget,
            programs: self.programs,
            result: self.result,
            input_decoder: Decoder::default(),
        })
    }
}

/// A front end's specification meets the invariants a decoded one has: a nonempty main module,
/// and an entry and include directories that stay inside the manifest's directory.
fn bound_spec(spec: &SpecSection) -> Result<(), ManifestError> {
    relative_path(&Value::String(spec.entry.clone()), "spec.entry")?;
    for (i, dir) in spec.include_dirs.iter().enumerate() {
        relative_path(
            &Value::String(dir.clone()),
            &format!("spec.include_dirs[{i}]"),
        )?;
    }
    string(&Value::String(spec.main_module.clone()), "spec.main_module")?;
    if let Some(module) = &spec.syntax_module {
        string(&Value::String(module.clone()), "spec.syntax_module")?;
    }
    Ok(())
}

impl FlowManifest {
    /// Read and decode the manifest at `path`; its directory becomes the root. A KRS corpus
    /// (`[spec] krs`) is the error ``spec.krs: a KRS corpus: run `krs kink <command>` in the
    /// package`` ([`ManifestFile::bind`]).
    pub fn read(path: &Path) -> Result<Self, ManifestError> {
        ManifestFile::read(path)?.bind(None)
    }

    /// Decode manifest `text` whose paths are relative to `directory`
    /// ([`ManifestFile::decode`], then [`ManifestFile::bind`] with no specification).
    pub fn decode(text: &str, directory: &Path) -> Result<Self, ManifestError> {
        ManifestFile::decode(text, directory)?.bind(None)
    }

    /// This manifest with `decoder` reading its programs' typed inputs: a front end that knows
    /// the inputs' declared types (the krs front end) sets it on the manifest it decoded.
    #[must_use]
    pub fn with_input_decoder(mut self, decoder: Arc<dyn InputDecoder + Send + Sync>) -> Self {
        self.input_decoder = Decoder(Some(decoder));
        self
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

fn spec(value: &Value) -> Result<SpecDecl, ManifestError> {
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
            "assume_joined",
            "krs",
        ],
    )?;
    if let Some(krs) = spec.get("krs") {
        if let Some(key) = K_SPEC_KEYS.iter().find(|key| spec.contains_key(**key)) {
            return Err(ManifestError::new(
                join("spec", key),
                "not allowed with spec.krs: the krs front end supplies it",
            ));
        }
        let krs = table(krs, "spec.krs")?;
        known_keys(krs, "spec.krs", &["definition"])?;
        return Ok(SpecDecl::Krs(KrsSpec {
            definition: required_string(krs, "spec.krs", "definition")?,
            assume_joined: assume_joined(spec)?,
        }));
    }
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
    let assume_joined = assume_joined(spec)?;
    Ok(SpecDecl::K(SpecSection {
        entry,
        main_module: required_string(spec, "spec", "main_module")?,
        syntax_module: optional_string(spec, "spec", "syntax_module")?,
        include_dirs,
        md_selector: optional_string(spec, "spec", "md_selector")?
            .unwrap_or_else(|| DEFAULT_MD_SELECTOR.to_owned()),
        assume_joined,
    }))
}

/// `[spec] assume_joined`: sorted, without repeats.
fn assume_joined(spec: &Table) -> Result<Vec<String>, ManifestError> {
    let mut assume_joined = match spec.get("assume_joined") {
        None => Vec::new(),
        Some(Value::Array(names)) => names
            .iter()
            .enumerate()
            .map(|(i, name)| match name {
                Value::String(name) if !name.trim().is_empty() => Ok(name.clone()),
                _ => Err(ManifestError::new(
                    format!("spec.assume_joined[{i}]"),
                    "expected a nonempty string, a finding's name",
                )),
            })
            .collect::<Result<Vec<_>, _>>()?,
        Some(_) => {
            return Err(ManifestError::new(
                "spec.assume_joined",
                "expected an array of strings",
            ));
        }
    };
    assume_joined.sort();
    assume_joined.dedup();
    Ok(assume_joined)
}

fn budget(value: &Value) -> Result<Budget, ManifestError> {
    let budget = table(value, "budget")?;
    known_keys(budget, "budget", &["time_ms", "max_depth", "work_factor"])?;
    Ok(Budget {
        time_ms: positive(budget, "budget", "time_ms", DEFAULT_TIME_MS)?,
        max_depth: positive(budget, "budget", "max_depth", DEFAULT_MAX_DEPTH)?,
        work_factor: budget
            .contains_key("work_factor")
            .then(|| positive(budget, "budget", "work_factor", 1))
            .transpose()?,
    })
}

fn result(value: &Value) -> Result<ResultSection, ManifestError> {
    let section = table(value, "result")?;
    known_keys(section, "result", &["cells"])?;
    let key = "result.cells";
    let Some(Value::Array(entries)) = section.get("cells") else {
        return Err(match section.get("cells") {
            None => missing(key),
            Some(_) => ManifestError::new(key, "expected an array of cell names"),
        });
    };
    if entries.is_empty() {
        return Err(ManifestError::new(
            key,
            "must name at least one cell; without [result] every cell the specification does \
             not declare unobservable is compared",
        ));
    }
    let mut cells = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        let name = match entry {
            Value::String(name) if !name.is_empty() => name.clone(),
            Value::String(_) => {
                return Err(ManifestError::new(
                    key,
                    format!("entry {index} is empty: name a cell by its K name (`k` for <k>)"),
                ));
            }
            _ => {
                return Err(ManifestError::new(
                    key,
                    format!("entry {index} is not a string: name a cell by its K name"),
                ));
            }
        };
        if cells.contains(&name) {
            return Err(ManifestError::new(key, format!("names `{name}` twice")));
        }
        cells.push(name);
    }
    Ok(ResultSection { cells })
}

fn program(index: usize, value: &Value) -> Result<Program, ManifestError> {
    let position = format!("program[{index}]");
    let entry = table(value, &position)?;
    let id = required_string(entry, &position, "id")?;
    let key = program_key(&id);
    known_keys(
        entry,
        &key,
        &["id", "file", "text", "start_sort", "variables", "inputs"],
    )?;
    // Neither `file` nor `text`: a case of a definition without `$PGM`, whose variables are all
    // bound by name; admission refuses it on a definition that declares `$PGM`.
    let source = match (entry.get("file"), entry.get("text")) {
        (Some(file), None) => Some(ProgramSource::File(relative_path(
            file,
            &join(&key, "file"),
        )?)),
        (None, Some(Value::String(text))) => Some(ProgramSource::Text(text.clone())),
        (None, Some(_)) => {
            return Err(ManifestError::new(join(&key, "text"), "expected a string"));
        }
        (Some(_), Some(_)) => {
            return Err(ManifestError::new(
                key,
                "has both file and text; give at most one",
            ));
        }
        (None, None) => None,
    };
    let start_sort = optional_string(entry, &key, "start_sort")?;
    if source.is_none() && start_sort.is_some() {
        return Err(ManifestError::new(
            join(&key, "start_sort"),
            "start_sort applies to a program text; this program has none",
        ));
    }
    let inputs = match entry.get("inputs") {
        None => Table::new(),
        Some(Value::Table(inputs)) => {
            if let Some(name) = inputs.keys().find(|name| name.is_empty()) {
                return Err(ManifestError::new(
                    join(&join(&key, "inputs"), name),
                    "empty input name",
                ));
            }
            inputs.clone()
        }
        Some(_) => {
            return Err(ManifestError::new(
                join(&key, "inputs"),
                "expected a table of typed inputs by name",
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
        start_sort,
        variables,
        inputs,
    })
}
