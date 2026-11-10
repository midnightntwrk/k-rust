//! `[[patterns]]`: where the corpus's patterns are declared, as `[[program]]` declares its
//! programs.
//!
//! Each entry has exactly one of two keys:
//! - `files = "GLOB"`: kink pattern lists (`[[pattern]]` tables, `crate::pattern`), matched by
//!   the glob semantics of `[[program]] files` and `cases` under the manifest's directory. As for
//!   `cases`, the glob may name one file without a wildcard, and its last component must end in
//!   `.toml`, since a pattern list is a TOML document.
//! - `krs = "PACKAGE"`: a KRS patterns package, whose patterns a front end that compiles KRS
//!   provides (`crate::cli::FrontEnd::krs_patterns`).
//!
//! The globs are matched when the manifest is decoded, so a glob that matches nothing is a
//! manifest error, as it is for programs, and two entries that match one file are an error: a
//! pattern list is declared once. The lists are read by the commands that ask patterns (`query`,
//! `fuzz --pattern`), so their contents are those commands' input, as a mutation list is `run`'s,
//! and no other command reads them. No part of `[[patterns]]` enters a digest or a key: a pattern
//! decides no result, outcome or verdict.

use super::{Matches, join, known_keys, pattern_matches, string, table};
use crate::ManifestError;
use std::{collections::BTreeMap, path::Path};
use toml::Value;

/// One `[[patterns]]` entry ([`super::FlowManifest::patterns`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternsEntry {
    /// `files = "GLOB"`: the pattern lists `glob` matches, each a path relative to the manifest's
    /// directory as matched, sorted by path.
    Files { glob: String, matches: Vec<String> },
    /// `krs = "PACKAGE"`: the KRS patterns package `package`.
    Krs { package: String },
}

impl PatternsEntry {
    /// The key of the entry at `index` in the manifest: `patterns[<index>].files` or
    /// `patterns[<index>].krs`.
    #[must_use]
    pub fn key(&self, index: usize) -> String {
        let name = match self {
            Self::Files { .. } => "files",
            Self::Krs { .. } => "krs",
        };
        join(&position(index), name)
    }
}

fn position(index: usize) -> String {
    format!("patterns[{index}]")
}

/// The `[[patterns]]` entries of `value`, the manifest's `patterns`, whose globs are matched
/// under `directory`, in declaration order.
pub(super) fn entries(
    value: &Value,
    directory: &Path,
) -> Result<Vec<PatternsEntry>, ManifestError> {
    let Value::Array(entries) = value else {
        return Err(ManifestError::new(
            "patterns",
            "expected [[patterns]] tables",
        ));
    };
    let mut decoded = Vec::with_capacity(entries.len());
    // The entry that first matched each file, and that first named each package, for an
    // overlap's error.
    let mut matched = BTreeMap::<String, String>::new();
    let mut packages = BTreeMap::<String, String>::new();
    for (index, entry) in entries.iter().enumerate() {
        let position = position(index);
        let entry = table(entry, &position)?;
        known_keys(entry, &position, &["files", "krs"])?;
        let decl = match (entry.get("files"), entry.get("krs")) {
            (Some(_), Some(_)) => {
                return Err(ManifestError::new(
                    position,
                    "has both files and krs; give one",
                ));
            }
            (None, None) => {
                return Err(ManifestError::new(
                    position,
                    "names no patterns: give files = \"GLOB\" (kink pattern lists) or krs = \
                     \"PACKAGE\" (a KRS patterns package)",
                ));
            }
            (Some(glob), None) => {
                let key = join(&position, "files");
                let matches = pattern_matches(glob, &key, directory, Matches::PatternLists)?;
                for file in &matches {
                    if let Some(first) = matched.get(file) {
                        return Err(ManifestError::new(
                            &key,
                            format!(
                                "matches {file:?}, which {first} also matches; a pattern list is \
                                 declared once"
                            ),
                        ));
                    }
                    matched.insert(file.clone(), key.clone());
                }
                PatternsEntry::Files {
                    glob: string(glob, &key)?,
                    matches,
                }
            }
            (None, Some(package)) => {
                let key = join(&position, "krs");
                let package = string(package, &key)?;
                if let Some(first) = packages.get(&package) {
                    return Err(ManifestError::new(
                        &key,
                        format!(
                            "{first} also names the package {package:?}; a package is declared once"
                        ),
                    ));
                }
                packages.insert(package.clone(), key);
                PatternsEntry::Krs { package }
            }
        };
        decoded.push(decl);
    }
    Ok(decoded)
}

#[cfg(test)]
mod tests {
    use super::PatternsEntry;
    use crate::{FlowManifest, ManifestError};
    use std::{
        fs,
        path::{Path, PathBuf},
    };

    const SPEC: &str = "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\n";

    /// A fresh corpus directory holding `files` (empty pattern lists).
    fn corpus(name: &str, files: &[&str]) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "kink-flow-pattern-sources-{name}-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&dir);
        for file in files {
            let path = dir.join(file);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, "").unwrap();
        }
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn decode(dir: &Path, patterns: &str) -> Result<FlowManifest, ManifestError> {
        FlowManifest::decode(&format!("{SPEC}{patterns}"), dir)
    }

    #[track_caller]
    fn refused(dir: &Path, patterns: &str, key: &str, message: &str) {
        let error = decode(dir, patterns).expect_err("the manifest must be refused");
        assert_eq!(error.key, key, "{error}");
        assert!(error.message.contains(message), "{error}");
    }

    /// `files` matches pattern lists by the program globs' semantics, `krs` names a package, and
    /// the entries keep their declaration order; a manifest without the table declares none.
    #[test]
    fn files_and_krs_entries_decode_in_declaration_order() {
        let dir = corpus(
            "decode",
            &["patterns/bus.toml", "patterns/alu.toml", "PATTERNS.toml"],
        );
        let manifest = decode(
            &dir,
            "[[patterns]]\nkrs = \"sm83-patterns\"\n\n[[patterns]]\nfiles = \"patterns/*.toml\"\n\n\
             [[patterns]]\nfiles = \"PATTERNS.toml\"\n",
        )
        .unwrap();
        assert_eq!(
            manifest.patterns,
            [
                PatternsEntry::Krs {
                    package: "sm83-patterns".into()
                },
                // Sorted by path, whatever order the directory lists them in.
                PatternsEntry::Files {
                    glob: "patterns/*.toml".into(),
                    matches: vec!["patterns/alu.toml".into(), "patterns/bus.toml".into()],
                },
                // A pattern list may be named without a wildcard, as a case document may.
                PatternsEntry::Files {
                    glob: "PATTERNS.toml".into(),
                    matches: vec!["PATTERNS.toml".into()],
                },
            ]
        );
        assert_eq!(manifest.patterns[0].key(0), "patterns[0].krs");
        assert_eq!(manifest.patterns[1].key(1), "patterns[1].files");
        assert!(decode(&dir, "").unwrap().patterns.is_empty());
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_patterns_entry_has_exactly_one_known_key() {
        let dir = corpus("refusals", &["patterns/a.toml", "patterns/notes.md"]);
        refused(
            &dir,
            "[[patterns]]\nfiles = \"patterns/*.toml\"\nkrs = \"p\"\n",
            "patterns[0]",
            "has both files and krs; give one",
        );
        refused(&dir, "[[patterns]]\n", "patterns[0]", "names no patterns");
        refused(
            &dir,
            "[[patterns]]\nfiles = \"patterns/*.toml\"\nid = \"x\"\n",
            "patterns[0].id",
            "unknown key",
        );
        refused(
            &dir,
            "[[patterns]]\nkrs = \"\"\n",
            "patterns[0].krs",
            "must not be empty",
        );
        refused(
            &dir,
            "[[patterns]]\nfiles = 3\n",
            "patterns[0].files",
            "expected a string",
        );
        let error = FlowManifest::decode(&format!("patterns = 3\n{SPEC}"), &dir).unwrap_err();
        assert_eq!(
            error.to_string(),
            "patterns: expected [[patterns]] tables",
            "{error}"
        );
        // A glob that matches nothing is refused, as a program glob is.
        refused(
            &dir,
            "[[patterns]]\nfiles = \"patterns/*.toml\"\n\n[[patterns]]\nfiles = \"more/*.toml\"\n",
            "patterns[1].files",
            "matches no file in the manifest's directory",
        );
        // A pattern list is a TOML document.
        refused(
            &dir,
            "[[patterns]]\nfiles = \"patterns/*\"\n",
            "patterns[0].files",
            "pattern lists are TOML",
        );
        // A glob of the program globs' grammar only.
        refused(
            &dir,
            "[[patterns]]\nfiles = \"patterns/[ab].toml\"\n",
            "patterns[0].files",
            "no character classes",
        );
        refused(
            &dir,
            "[[patterns]]\nfiles = \"/patterns/a.toml\"\n",
            "patterns[0].files",
            "absolute",
        );
        // A list, or a package, is declared once.
        refused(
            &dir,
            "[[patterns]]\nfiles = \"patterns/*.toml\"\n\n[[patterns]]\nfiles = \"patterns/a.toml\"\n",
            "patterns[1].files",
            "matches \"patterns/a.toml\", which patterns[0].files also matches",
        );
        refused(
            &dir,
            "[[patterns]]\nkrs = \"p\"\n\n[[patterns]]\nkrs = \"p\"\n",
            "patterns[1].krs",
            "patterns[0].krs also names the package \"p\"",
        );
        let _ = fs::remove_dir_all(&dir);
    }
}
