use std::fs;
use std::path::{Path, PathBuf};

use k_rust::kore::parser::{parse_definition, parse_pattern};

const PASS_DEFINITION_COUNT: usize = 73;
const FAIL_DEFINITION_COUNT: usize = 9;
const SCALA_COMPAT_DEFINITION_COUNT: usize = 1;
const PATTERN_COUNT: usize = 4;

#[test]
fn parses_reference_definitions() {
    let fixtures = fixtures("definitions/pass");
    assert_eq!(fixtures.len(), PASS_DEFINITION_COUNT);

    for path in fixtures {
        assert_definition_round_trip(&path);
    }
}

#[test]
fn rejects_malformed_reference_definitions() {
    let fixtures = fixtures("definitions/fail");
    assert_eq!(fixtures.len(), FAIL_DEFINITION_COUNT);

    let accepted: Vec<_> = fixtures
        .iter()
        .filter(|path| parse_definition(&read(path)).is_ok())
        .map(|path| path.display().to_string())
        .collect();
    assert!(
        accepted.is_empty(),
        "unexpectedly accepted:\n{}",
        accepted.join("\n")
    );
}

#[test]
fn parses_standalone_reference_patterns() {
    let fixtures = fixtures("patterns");
    assert_eq!(fixtures.len(), PATTERN_COUNT);

    for path in fixtures {
        assert_pattern_round_trip(&path);
    }
}

#[test]
fn preserves_scala_unknown_escape_compatibility() {
    let fixtures = fixtures("definitions/scala-compat");
    assert_eq!(fixtures.len(), SCALA_COMPAT_DEFINITION_COUNT);

    for path in fixtures {
        assert_definition_round_trip(&path);
    }
}

fn assert_definition_round_trip(path: &Path) {
    let definition =
        parse_definition(&read(path)).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
    let printed = definition.to_string();
    let reparsed = parse_definition(&printed)
        .unwrap_or_else(|error| panic!("{} after printing: {error}\n\n{printed}", path.display()));
    assert_eq!(reparsed, definition, "{}", path.display());
}

fn assert_pattern_round_trip(path: &Path) {
    let pattern =
        parse_pattern(&read(path)).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
    let printed = pattern.to_string();
    let reparsed = parse_pattern(&printed)
        .unwrap_or_else(|error| panic!("{} after printing: {error}\n\n{printed}", path.display()));
    assert_eq!(reparsed, pattern, "{}", path.display());
}

fn fixtures(relative: &str) -> Vec<PathBuf> {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/kore")
        .join(relative);
    let mut fixtures: Vec<_> = fs::read_dir(&directory)
        .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
        .map(|entry| entry.expect("fixture entry should be readable").path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "kore")
        })
        .collect();
    fixtures.sort();
    fixtures
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}
