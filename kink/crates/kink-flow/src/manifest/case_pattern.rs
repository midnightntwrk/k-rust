//! The pattern of a `[[program]]` entry's `files` or `cases`: which case files under the
//! manifest's directory it matches, as their paths relative to that directory.
//!
//! A pattern is components separated by `/`. A component is a literal name; a glob of literal
//! characters, `*` (any run of characters) and `?` (one character); or exactly `**` (zero or more
//! directories). A trailing `**` matches every file below its directory. A match is a path
//! relative to the manifest's directory, written as it was matched (components joined by `/`),
//! which is the program's id: a function of where the case is, never of the host, of the
//! directory's absolute path or of the order the file system lists entries in.
//!
//! - A wildcard never matches a name that starts with `.`: a glob matches one only when its own
//!   first character is a literal `.`, and `**` never enters one; a literal component may name
//!   one. The cache directory (`.kink-flow/`), editor files and version-control state live in
//!   the manifest's directory, and a corpus must not depend on them.
//! - `**` descends into real directories only, never through a link, so a link cycle cannot make
//!   the walk infinite; literal and glob components follow links, a walk bounded by the pattern's
//!   length. Where a link leads is checked when the case file is read (inside the manifest's
//!   directory, by the program-file rule).
//! - A match is a regular file, links followed, or a link that does not resolve (dangling, or a
//!   cycle), so that reading it fails loudly instead of the case disappearing. A directory is no
//!   match. A named pipe, socket or device the pattern matches is an error: reading one can block
//!   for good, and no case can be read from it.
//! - A name that is not UTF-8 is an error when the pattern matches a path through it (the name
//!   read lossily), since no program id can name that match; any other such name is ignored, as
//!   every name the pattern does not match is.
//! - The matches are sorted by their path and without repeats (one file reached twice by `**` is
//!   one match).

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
};

/// A parsed pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CasePattern {
    components: Vec<Part>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Part {
    /// A name without wildcards.
    Literal(String),
    /// A name with `*` or `?`.
    Glob(Vec<Token>),
    /// `**`.
    AnyDirectories,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Token {
    Char(char),
    /// `*`
    Run,
    /// `?`
    One,
}

impl CasePattern {
    /// Parse `text`, a pattern matched under the tree messages name `tree`. The error is the
    /// reason the pattern is refused.
    pub(super) fn parse(text: &str, tree: &str) -> Result<Self, String> {
        if text.is_empty() {
            return Err("must not be empty".into());
        }
        if let Some(c) = text
            .chars()
            .find(|c| matches!(c, '\\' | '[' | ']' | '{' | '}'))
        {
            return Err(format!(
                "pattern {text:?} has `{c}`: a pattern has `*`, `?` and `**` only (no character \
                 classes, alternatives or escapes)"
            ));
        }
        if text.starts_with('/') {
            return Err(format!(
                "pattern {text:?} is absolute: a pattern is relative to {tree}"
            ));
        }
        let mut components = Vec::new();
        for component in text.split('/') {
            components.push(match component {
                "" => {
                    return Err(format!(
                        "pattern {text:?} has an empty component (`//` or a trailing `/`)"
                    ));
                }
                "." | ".." => {
                    return Err(format!(
                        "pattern {text:?} has a `{component}` component: a pattern names the \
                         directories it walks, down from {tree}"
                    ));
                }
                "**" => Part::AnyDirectories,
                _ if component.contains("**") => {
                    return Err(format!(
                        "pattern {text:?}: `**` is a whole component (`a/**/b`), not part of a \
                         name"
                    ));
                }
                _ if component.contains(['*', '?']) => Part::Glob(
                    component
                        .chars()
                        .map(|c| match c {
                            '*' => Token::Run,
                            '?' => Token::One,
                            c => Token::Char(c),
                        })
                        .collect(),
                ),
                _ => Part::Literal(component.to_owned()),
            });
        }
        // A trailing `**` matches every file below: `**/*`.
        if components.last() == Some(&Part::AnyDirectories) {
            components.push(Part::Glob(vec![Token::Run]));
        }
        Ok(Self { components })
    }

    /// Whether some component is a glob or `**`; a pattern without one names one path.
    pub(super) fn has_wildcard(&self) -> bool {
        self.components
            .iter()
            .any(|part| !matches!(part, Part::Literal(_)))
    }

    /// The paths under `root` that match, relative to `root`, sorted and without repeats. The
    /// error names the directory that cannot be listed or the name that is not UTF-8.
    pub(super) fn matches(&self, root: &Path) -> Result<Vec<String>, String> {
        let mut found = BTreeSet::new();
        walk(root, "", &self.components, &mut found)?;
        Ok(found.into_iter().collect())
    }
}

/// Extend `found` with the matches of `parts` under `directory`, whose path relative to the
/// manifest's directory is `at` (empty for the manifest's directory itself).
fn walk(
    directory: &Path,
    at: &str,
    parts: &[Part],
    found: &mut BTreeSet<String>,
) -> Result<(), String> {
    let Some((part, rest)) = parts.split_first() else {
        return Ok(());
    };
    match part {
        Part::Literal(name) => visit(&directory.join(name), &child(at, name), rest, found),
        Part::Glob(tokens) => {
            // A glob matches a dot name only by its own literal `.`.
            let dot = tokens.first() == Some(&Token::Char('.'));
            for entry in entries(directory, at)? {
                if (dot || !entry.name.starts_with('.'))
                    && glob(tokens, &entry.name.chars().collect::<Vec<_>>())
                {
                    through(&entry, found, |found| {
                        visit(&entry.path, &entry.at, rest, found)
                    })?;
                }
            }
            Ok(())
        }
        Part::AnyDirectories => {
            // Zero directories, then one more real (not linked) directory at a time.
            walk(directory, at, rest, found)?;
            for entry in entries(directory, at)? {
                let real_directory = fs::symlink_metadata(&entry.path).is_ok_and(|m| m.is_dir());
                if !entry.name.starts_with('.') && real_directory {
                    through(&entry, found, |found| {
                        walk(&entry.path, &entry.at, parts, found)
                    })?;
                }
            }
            Ok(())
        }
    }
}

/// The path of the entry `name` of the directory written `at`.
fn child(at: &str, name: &str) -> String {
    if at.is_empty() {
        name.to_owned()
    } else {
        format!("{at}/{name}")
    }
}

/// `path` (written `at`) matched one component: the last component's match when nothing follows
/// (a regular file, or a link that does not resolve); else the directory the rest of the pattern
/// is matched in.
fn visit(path: &Path, at: &str, rest: &[Part], found: &mut BTreeSet<String>) -> Result<(), String> {
    let target = fs::metadata(path);
    if !rest.is_empty() {
        return match target {
            Ok(metadata) if metadata.is_dir() => walk(path, at, rest, found),
            _ => Ok(()),
        };
    }
    match target {
        Ok(metadata) if metadata.is_file() => {
            found.insert(at.to_owned());
        }
        Ok(metadata) if metadata.is_dir() => {}
        Ok(_) => {
            return Err(format!(
                "{at} matches and is not a regular file (a named pipe, socket or device): a case \
                 is read from a file"
            ));
        }
        // A link that does not resolve matches, and is refused when it is read.
        Err(_) if fs::symlink_metadata(path).is_ok() => {
            found.insert(at.to_owned());
        }
        Err(_) => {}
    }
    Ok(())
}

/// An entry of a listed directory.
struct Entry {
    /// Its name, read lossily when it is not UTF-8.
    name: String,
    /// Whether its name is UTF-8.
    utf8: bool,
    /// Its path relative to the manifest's directory, written with `name`.
    at: String,
    path: PathBuf,
}

/// Run `search`, the pattern's rest matched at or below `entry`, into `found`. Below a name that
/// is not UTF-8 a match is an error, since no program id can name it; without one the name is
/// ignored.
fn through(
    entry: &Entry,
    found: &mut BTreeSet<String>,
    search: impl FnOnce(&mut BTreeSet<String>) -> Result<(), String>,
) -> Result<(), String> {
    if entry.utf8 {
        return search(found);
    }
    let mut lost = BTreeSet::new();
    search(&mut lost)?;
    match lost.first() {
        None => Ok(()),
        Some(first) => Err(format!(
            "the pattern matches {first} (read lossily), whose path has the name {:?}, which is \
             not UTF-8: no program id can name it",
            entry.name
        )),
    }
}

/// The entries of `directory` (written `at`).
fn entries(directory: &Path, at: &str) -> Result<Vec<Entry>, String> {
    let shown = if at.is_empty() { "." } else { at };
    let listing = match fs::read_dir(directory) {
        Ok(listing) => listing,
        // A directory the pattern names that does not exist has no matches.
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) if e.kind() == std::io::ErrorKind::NotADirectory => return Ok(Vec::new()),
        Err(e) => return Err(format!("cannot list {shown}: {e}")),
    };
    let mut entries = Vec::new();
    for entry in listing {
        let entry = entry.map_err(|e| format!("cannot list {shown}: {e}"))?;
        let file_name = entry.file_name();
        let (name, utf8) = match file_name.to_str() {
            Some(name) => (name.to_owned(), true),
            None => (file_name.to_string_lossy().into_owned(), false),
        };
        entries.push(Entry {
            at: child(at, &name),
            name,
            utf8,
            path: entry.path(),
        });
    }
    Ok(entries)
}

/// Whether `name` matches the glob `tokens` (`*` any run, `?` one character). Greedy, in time
/// linear in `name` per token: on a mismatch only the last `*` takes one more character, since
/// a match that an earlier `*` could reach by taking more the last one reaches as well.
fn glob(tokens: &[Token], name: &[char]) -> bool {
    let (mut token, mut at) = (0, 0);
    // The token after the last `*` and the first character that `*` has not taken.
    let mut last_run = None;
    while at < name.len() {
        match tokens.get(token) {
            Some(Token::Run) => {
                token += 1;
                last_run = Some((token, at));
            }
            Some(Token::One) => (token, at) = (token + 1, at + 1),
            Some(Token::Char(c)) if *c == name[at] => (token, at) = (token + 1, at + 1),
            _ => match last_run {
                Some((after, taken)) => {
                    (token, at) = (after, taken + 1);
                    last_run = Some((after, taken + 1));
                }
                None => return false,
            },
        }
    }
    tokens[token..].iter().all(|token| *token == Token::Run)
}

impl CasePattern {
    /// Whether the last component is a literal or a glob whose text ends with `suffix`, so that
    /// every match ends with it.
    pub(super) fn ends_with(&self, suffix: &str) -> bool {
        let tail = match self.components.last() {
            Some(Part::Literal(name)) => name.clone(),
            Some(Part::Glob(tokens)) => {
                let literal = tokens
                    .iter()
                    .rev()
                    .take_while(|token| matches!(token, Token::Char(_)))
                    .map(|token| match token {
                        Token::Char(c) => *c,
                        _ => unreachable!(),
                    })
                    .collect::<Vec<_>>();
                literal.into_iter().rev().collect()
            }
            _ => String::new(),
        };
        tail.ends_with(suffix)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn matches(pattern: &str, name: &str) -> bool {
        let Part::Glob(tokens) = &CasePattern::parse(pattern, "the manifest\'s directory")
            .unwrap()
            .components[0]
        else {
            panic!("not a glob")
        };
        glob(tokens, &name.chars().collect::<Vec<_>>())
    }

    #[test]
    fn globs_match_runs_and_single_characters() {
        assert!(matches("*.imp", "sum.imp"));
        assert!(matches("*.imp", ".imp"));
        assert!(!matches("*.imp", "sum.imp.bak"));
        assert!(matches("t?st*", "test1"));
        assert!(!matches("t?st", "tst"));
        assert!(matches("a*a", "aa"));
        assert!(matches("*", "x"));
        assert!(matches("*", ""));
        assert!(matches("a*b*c", "aXbYbc"));
        assert!(!matches("a*b*c", "aXbYb"));
        assert!(matches("*a?", "bab"));
        assert!(!matches("*a?", "ba"));
    }

    /// Many `*` against a long name that almost matches are decided in time linear per token.
    #[test]
    fn globs_with_many_runs_are_decided_quickly() {
        let name = "a".repeat(200).chars().collect::<Vec<_>>();
        let Part::Glob(tokens) =
            &CasePattern::parse("*a*a*a*a*a*a*a*b", "the manifest\'s directory")
                .unwrap()
                .components[0]
        else {
            panic!("not a glob")
        };
        assert!(!glob(tokens, &name));
        let mut almost = name.clone();
        almost.push('b');
        assert!(glob(tokens, &almost));
    }

    #[test]
    fn a_suffix_holds_when_every_match_ends_with_it() {
        assert!(
            CasePattern::parse("cases/*/case.toml", "the manifest\'s directory")
                .unwrap()
                .ends_with(".toml")
        );
        assert!(
            CasePattern::parse("cases/*.toml", "the manifest\'s directory")
                .unwrap()
                .ends_with(".toml")
        );
        assert!(
            !CasePattern::parse("cases/*", "the manifest\'s directory")
                .unwrap()
                .ends_with(".toml")
        );
        assert!(
            !CasePattern::parse("cases/*.to?l", "the manifest\'s directory")
                .unwrap()
                .ends_with(".toml")
        );
        assert!(
            !CasePattern::parse("cases/**", "the manifest\'s directory")
                .unwrap()
                .ends_with(".toml")
        );
    }
}
