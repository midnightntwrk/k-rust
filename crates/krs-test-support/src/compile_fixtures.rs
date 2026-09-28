//! Directory-discovered compile fixtures checked against directives in their source.

use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Output;

use serde_json::Value;

use crate::cargo_fixture;

/// What a compile fixture states about its own `cargo check` outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expectation {
    /// The fixture carries `//@ check-pass` and must compile without errors.
    CheckPass,
    /// The fixture carries this many `//~ ERROR` directives and must fail to compile.
    Errors(usize),
}

impl fmt::Display for Expectation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CheckPass => formatter.write_str("check-pass"),
            Self::Errors(count) => write!(formatter, "ERROR x{count}"),
        }
    }
}

struct Directive {
    line: usize,
    fragment: String,
}

struct Fixture {
    name: String,
    path: PathBuf,
    check_pass: bool,
    errors: Vec<Directive>,
}

impl Fixture {
    fn expectation(&self) -> Expectation {
        if self.check_pass {
            Expectation::CheckPass
        } else {
            Expectation::Errors(self.errors.len())
        }
    }
}

struct Diagnostic {
    line: Option<usize>,
    message: String,
}

/// Check every binary fixture of a Cargo package against the directives in its source.
///
/// Fixtures are the `src/bin/*.rs` files next to `manifest`, which Cargo discovers as binaries.
/// All of them are checked by one `cargo check --bins --keep-going`.
/// Each fixture states its outcome in the rustc UI-test convention:
///
/// - `//@ check-pass` on a line of its own: the fixture compiles without errors;
/// - `//~ ERROR <fragment>` at the end of a line: an error whose message contains `<fragment>` has its primary span on that line;
/// - `//~^ ERROR <fragment>`: the same for the line above, one line further up per additional `^`.
///
/// A primary span inside a macro expansion is attributed to the first call site in the fixture.
/// A fixture must carry either `check-pass` or at least one `ERROR` directive, so a new file cannot go unchecked.
/// Errors without a directive do not fail a compile-fail fixture.
///
/// Returns the fixture names in sorted order with their expectations.
///
/// # Panics
///
/// Panics with every mismatch if a fixture is malformed or a directive does not match the compiler diagnostics.
#[must_use]
pub fn check_compile_fixtures(manifest: &Path) -> Vec<(String, Expectation)> {
    let root = manifest.parent().expect("fixture manifest has a parent");
    let mut failures = Vec::new();
    let fixtures = discover(&root.join("src/bin"), &mut failures);
    let output = cargo_fixture(manifest)
        .args(&["--bins", "--keep-going", "--message-format=json"])
        .check();
    let mut observed = observe(&output, root, &fixtures, &mut failures);
    let error_count: usize = observed.values().map(Vec::len).sum();
    for fixture in &fixtures {
        let diagnostics = observed.remove(&fixture.path).unwrap_or_default();
        compare(fixture, &diagnostics, &mut failures);
    }
    if output.status.success() && fixtures.iter().any(|fixture| !fixture.check_pass) {
        failures.push("cargo check unexpectedly succeeded with compile-fail fixtures".to_owned());
    }
    if !output.status.success() && error_count == 0 {
        failures.push(format!(
            "cargo check failed without fixture errors:\n{}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    fixtures
        .iter()
        .map(|fixture| (fixture.name.clone(), fixture.expectation()))
        .collect()
}

fn discover(bin: &Path, failures: &mut Vec<String>) -> Vec<Fixture> {
    let mut paths: Vec<_> = std::fs::read_dir(bin)
        .expect("binary fixture directory exists")
        .map(|entry| entry.expect("binary fixture entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "rs"))
        .collect();
    paths.sort();
    if paths.is_empty() {
        failures.push(format!("{}: no binary fixtures found", bin.display()));
    }
    paths
        .iter()
        .map(|path| parse_fixture(path, failures))
        .collect()
}

fn parse_fixture(path: &Path, failures: &mut Vec<String>) -> Fixture {
    let name = path
        .file_stem()
        .expect("fixture has a name")
        .to_string_lossy()
        .into_owned();
    let source = std::fs::read_to_string(path).expect("fixture source is readable");
    let mut check_pass = false;
    let mut errors = Vec::new();
    for (index, line) in source.lines().enumerate() {
        let line_number = index + 1;
        if line.trim() == "//@ check-pass" {
            if check_pass {
                failures.push(format!(
                    "{name}:{line_number}: duplicate check-pass directive"
                ));
            }
            check_pass = true;
        }
        let Some((_, raw)) = line.split_once("//~") else {
            continue;
        };
        let directive = raw.trim_start_matches('^');
        let carets = raw.len() - directive.len();
        let target = line_number.checked_sub(carets).filter(|line| *line > 0);
        match (target, directive.trim().strip_prefix("ERROR ")) {
            (Some(line), Some(fragment)) if !fragment.is_empty() => errors.push(Directive {
                line,
                fragment: fragment.to_owned(),
            }),
            _ => failures.push(format!("{name}:{line_number}: invalid ERROR directive")),
        }
    }
    if check_pass != errors.is_empty() {
        failures.push(format!(
            "{name}: fixture must have either ERROR directives or one check-pass directive"
        ));
    }
    Fixture {
        name,
        path: path.canonicalize().expect("fixture path exists"),
        check_pass,
        errors,
    }
}

/// Collect the error diagnostics of each fixture from Cargo's JSON message stream.
fn observe(
    output: &Output,
    root: &Path,
    fixtures: &[Fixture],
    failures: &mut Vec<String>,
) -> BTreeMap<PathBuf, Vec<Diagnostic>> {
    let mut observed: BTreeMap<PathBuf, Vec<Diagnostic>> = BTreeMap::new();
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        let Ok(record) = serde_json::from_str::<Value>(line) else {
            failures.push(format!("invalid Cargo JSON record: {line}"));
            continue;
        };
        if record["reason"] != "compiler-message" || record["message"]["level"] != "error" {
            continue;
        }
        let Some(source) = record["target"]["src_path"].as_str() else {
            failures.push("compiler error has no target source path".to_owned());
            continue;
        };
        let Some(message) = record["message"]["message"].as_str() else {
            failures.push(format!("{source}: compiler error has no message"));
            continue;
        };
        let source = PathBuf::from(source);
        let source = source.canonicalize().unwrap_or(source);
        if !fixtures.iter().any(|fixture| fixture.path == source) {
            continue;
        }
        let line = record["message"]["spans"]
            .as_array()
            .and_then(|spans| spans.iter().find(|span| span["is_primary"] == true))
            .and_then(|span| span_line_in_fixture(span, &source, root));
        observed.entry(source).or_default().push(Diagnostic {
            line,
            message: message.to_owned(),
        });
    }
    observed
}

fn compare(fixture: &Fixture, diagnostics: &[Diagnostic], failures: &mut Vec<String>) {
    let actual = || {
        if diagnostics.is_empty() {
            return "none".to_owned();
        }
        diagnostics
            .iter()
            .map(|diagnostic| match diagnostic.line {
                Some(line) => format!("line {line}: {}", diagnostic.message),
                None => format!("line unknown: {}", diagnostic.message),
            })
            .collect::<Vec<_>>()
            .join("; ")
    };
    if fixture.check_pass {
        if !diagnostics.is_empty() {
            failures.push(format!(
                "{}: check-pass expected no errors; observed: {}",
                fixture.name,
                actual()
            ));
        }
        return;
    }
    for directive in &fixture.errors {
        let matched = diagnostics.iter().any(|diagnostic| {
            diagnostic.line == Some(directive.line)
                && diagnostic.message.contains(&directive.fragment)
        });
        if !matched {
            failures.push(format!(
                "{}:{}: expected ERROR {:?}; observed: {}",
                fixture.name,
                directive.line,
                directive.fragment,
                actual()
            ));
        }
    }
}

/// Resolve a span to its line in `fixture`, following macro call sites outward.
fn span_line_in_fixture(span: &Value, fixture: &Path, root: &Path) -> Option<usize> {
    let file = Path::new(span["file_name"].as_str()?);
    let path = if file.is_absolute() {
        file.to_path_buf()
    } else {
        root.join(file)
    };
    if path.canonicalize().ok().as_deref() == Some(fixture) {
        return span["line_start"]
            .as_u64()
            .and_then(|line| usize::try_from(line).ok());
    }
    let call_site = &span["expansion"]["span"];
    if call_site.is_object() {
        span_line_in_fixture(call_site, fixture, root)
    } else {
        None
    }
}
