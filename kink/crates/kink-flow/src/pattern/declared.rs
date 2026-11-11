//! The patterns a command asks: the list the command line names, else the patterns the corpus
//! declares in `FLOW.toml` (`[[patterns]]`, [`crate::manifest::PatternsEntry`]).
//!
//! **Precedence.** A list the command line names (kink-flow's `query FLOW.toml PATTERNS.toml`, a
//! `--patterns` flag, or a front end's own layout file) is the whole list, and the manifest's
//! `[[patterns]]` is not read, as a verb's own flag replaces a front end's mutation list. Without
//! one, the corpus's patterns are its `[[patterns]]`. A corpus that declares none, asked with no
//! list, is refused: there is no pattern to ask.
//!
//! **Order.** The declared patterns are, in order: the `[[patterns]]` entries as written; within a
//! `files` entry, the lists its glob matched, sorted by path; within a list, its `[[pattern]]`
//! tables in file order; within a `krs` entry, the patterns as the front end provides them. The
//! order is a function of the manifest and the files' contents, never of the order the file
//! system lists a directory in.
//!
//! **Ids.** A pattern's id is the one its author wrote, with no prefix naming its list, so moving
//! a pattern between lists keeps its answers, its cache records and its `[query]` lock row. Two
//! patterns of the assembled list with one id are an error naming both sources.
//!
//! **Sources.** Each pattern carries where it is written ([`PatternSource`]): a list's path
//! relative to the manifest's directory (or as the command line names it, when it is outside that
//! directory), or the KRS item a front end compiled it from. The query document reports it; no
//! digest or key holds it.
//!
//! **KRS packages.** A `krs` entry names a KRS patterns package, whose patterns only a front end
//! that compiles KRS provides ([`KrsPatternPackages`], `crate::cli::FrontEnd::krs_patterns`).
//! The front end is asked for a package only when the assembly reaches its entry, so a command
//! that names a list, and every command that asks no pattern, makes it compile none. kink-flow
//! itself compiles none, so it refuses such an entry, naming the krs front end's command: a
//! declared obligation is never silently skipped.

use super::{PatternEntry, PatternList, pattern_key};
use crate::manifest::{FlowManifest, ManifestError, PatternsEntry};
use serde_json::{Value, json};
use std::{collections::BTreeMap, fs, path::Path};

/// Where a pattern is written ([`PatternEntry::source`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternSource {
    /// A kink pattern list, by its path: relative to the manifest's directory where the list is
    /// inside it, else as the command line names it.
    File(String),
    /// A pattern a front end compiled from a KRS patterns package: the package as `[[patterns]]
    /// krs` names it, the item's path, and the source file and line the item is written at.
    Krs {
        package: String,
        item: String,
        file: String,
        line: u64,
    },
}

impl PatternSource {
    /// The source as the query document reports it: `{file}` or `{krs, item, file, line}`.
    #[must_use]
    pub fn value(&self) -> Value {
        match self {
            Self::File(file) => json!({"file": file}),
            Self::Krs {
                package,
                item,
                file,
                line,
            } => json!({"krs": package, "item": item, "file": file, "line": line}),
        }
    }

    /// The source as an error names it.
    fn shown(&self) -> String {
        match self {
            Self::File(file) => file.clone(),
            Self::Krs {
                package,
                item,
                file,
                line,
            } => format!("KRS package {package:?} item {item} ({file}:{line})"),
        }
    }
}

/// The patterns a front end compiles for the `[[patterns]] krs` packages of a manifest
/// ([`declared_patterns`]): for the package `package`, as the manifest names it, the package's
/// patterns, each with its [`PatternSource::Krs`] source, in the order the package writes them,
/// or why the front end provides none; `None` for a package the front end was not given. The
/// front end has checked each pattern as a list's is ([`super::WrittenPattern::checked`]), so
/// kink-flow takes them as they are, and checks only that their ids are unique across the
/// corpus's patterns and that their claims name programs of the corpus. It is asked only for a
/// package whose entry the assembly reaches, so a front end may compile a package when first
/// asked, and must give the same answer when asked again.
pub trait KrsPatternPackages: Sync {
    /// The patterns of `package`, or why there are none; `None` for a package not given.
    fn patterns(&self, package: &str) -> Option<&Result<Vec<PatternEntry>, String>>;
}

/// Each package's patterns, compiled beforehand ([`KrsPatternPackages`]).
pub type KrsPatterns = BTreeMap<String, Result<Vec<PatternEntry>, String>>;

impl KrsPatternPackages for KrsPatterns {
    fn patterns(&self, package: &str) -> Option<&Result<Vec<PatternEntry>, String>> {
        self.get(package)
    }
}

/// The refusal of a `[[patterns]] krs` entry where no front end provides KRS patterns.
pub const NO_KRS_FRONT_END: &str = "a KRS patterns package, which only the krs front end \
     compiles: run `krs kink query` (or `krs kink fuzz --pattern`) in the package";

/// The refusal of a command that names no pattern list on a corpus that declares no patterns.
pub const NO_PATTERNS: &str = "the corpus declares no patterns: declare them in FLOW.toml \
     (`[[patterns]] files = \"GLOB\"`, kink pattern lists; or `[[patterns]] krs = \"PACKAGE\"`, \
     a KRS patterns package), or name a pattern list";

/// The patterns a command asks (module docs): the list at `explicit` when the command line
/// names one, else the manifest's `[[patterns]]`, with `krs` the front end that compiles each
/// `krs` entry's package (`None` for a front end that compiles none). The error names the key,
/// and for a declared list's own error, the list.
pub fn declared_patterns(
    manifest: &FlowManifest,
    explicit: Option<&Path>,
    krs: Option<&dyn KrsPatternPackages>,
) -> Result<PatternList, ManifestError> {
    if let Some(path) = explicit {
        return PatternList::read_as(path, &shown_path(&manifest.directory, path));
    }
    if manifest.patterns.is_empty() {
        return Err(ManifestError::new("patterns", NO_PATTERNS));
    }
    let mut patterns = Vec::new();
    // Where each id was first written, for a duplicate's error.
    let mut origins = BTreeMap::<String, String>::new();
    let mut add = |entry: PatternEntry, origin: String| {
        if let Some(first) = origins.get(&entry.id) {
            return Err(ManifestError::new(
                pattern_key(&entry.id),
                format!("duplicate pattern id: {first} and {origin} both give it"),
            ));
        }
        origins.insert(entry.id.clone(), origin);
        patterns.push(entry);
        Ok(())
    };
    for (index, declared) in manifest.patterns.iter().enumerate() {
        match declared {
            PatternsEntry::Files { matches, .. } => {
                for file in matches {
                    for (at, entry) in read_declared(&manifest.directory, file)?
                        .patterns
                        .into_iter()
                        .enumerate()
                    {
                        add(entry, format!("{file} pattern[{at}]"))?;
                    }
                }
            }
            PatternsEntry::Krs { package } => {
                let key = declared.key(index);
                let provided = krs
                    .ok_or_else(|| ManifestError::new(&key, NO_KRS_FRONT_END))?
                    .patterns(package)
                    .ok_or_else(|| {
                        ManifestError::new(
                            &key,
                            format!(
                                "the front end provides no patterns of the package {package:?}"
                            ),
                        )
                    })?
                    .as_ref()
                    .map_err(|reason| ManifestError::new(&key, reason.clone()))?;
                for entry in provided {
                    let origin = entry
                        .source
                        .as_ref()
                        .map_or_else(|| format!("KRS package {package:?}"), PatternSource::shown);
                    add(entry.clone(), origin)?;
                }
            }
        }
    }
    Ok(PatternList { patterns })
}

/// The pattern list `file`, matched under the manifest's directory `directory`, read inside it by
/// the rule a program file is read by (links resolved, and refused when they lead outside it);
/// an error names the list, then the key.
fn read_declared(directory: &Path, file: &str) -> Result<PatternList, ManifestError> {
    let refused = |message: String| ManifestError::new(file, message);
    let root = fs::canonicalize(directory)
        .map_err(|e| refused(format!("cannot resolve the manifest's directory: {e}")))?;
    let resolved = fs::canonicalize(root.join(file))
        .map_err(|e| refused(format!("cannot read the pattern list: {e}")))?;
    if !resolved.starts_with(&root) {
        return Err(refused(
            "the pattern list escapes the manifest's directory".to_owned(),
        ));
    }
    PatternList::read_as(&resolved, file).map_err(|error| {
        ManifestError::new(
            if error.key.is_empty() {
                file.to_owned()
            } else {
                format!("{file} {}", error.key)
            },
            error.message,
        )
    })
}

/// `path` as a pattern's source names it: relative to the manifest's directory `directory`, by
/// `/`-separated components, where the file is inside it, else as given.
fn shown_path(directory: &Path, path: &Path) -> String {
    let inside = fs::canonicalize(directory)
        .ok()
        .zip(fs::canonicalize(path).ok())
        .and_then(|(root, file)| file.strip_prefix(&root).map(Path::to_path_buf).ok());
    match inside {
        Some(relative) => relative
            .components()
            .map(|component| component.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/"),
        None => path.display().to_string(),
    }
}
