use std::fs;
use std::path::{Path, PathBuf};

use k_rust::kore::parser::{parse_definition, parse_pattern};

const PASS_DEFINITION_COUNT: usize = 73;
const FAIL_DEFINITION_COUNT: usize = 10;
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
fn reference_kore_parser_grammar_verdicts() {
    let root =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/kore-syntax/grammar");
    let verdicts = read(&root.join("verdicts.tsv"));
    assert_eq!(
        verdicts,
        concat!(
            "pass/alias-set-variable.kore\t0\n",
            "pass/attribute-patterns.kore\t0\n",
            "pass/backslash-identifiers.kore\t0\n",
            "pass/legacy-multi-or.kore\t0\n",
            "pass/whitespace.kore.in\t0\n",
            "fail/alias-application-argument.kore\t1\n",
            "fail/assoc-and-head.kore\t1\n",
            "fail/empty-definition.kore\t1\n",
        )
    );

    let pass = fixtures_in(&root.join("pass"), "kore");
    assert_eq!(pass.len(), 4);
    for path in pass {
        assert_definition_round_trip(&path);
    }

    let template = read(&root.join("pass/whitespace.kore.in"));
    let whitespace = template.replace("<FF>", "\u{c}").replace("<VT>", "\u{b}");
    let definition = parse_definition(&whitespace).expect("reference whitespace should parse");
    assert_eq!(
        parse_definition(&definition.to_string()).unwrap(),
        definition
    );

    let fail = fixtures_in(&root.join("fail"), "kore");
    assert_eq!(fail.len(), 3);
    for path in fail {
        assert!(
            parse_definition(&read(&path)).is_err(),
            "unexpectedly accepted {}",
            path.display()
        );
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
    fixtures_in(&directory, "kore")
}

fn fixtures_in(directory: &Path, extension: &str) -> Vec<PathBuf> {
    let mut fixtures: Vec<_> = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
        .map(|entry| entry.expect("fixture entry should be readable").path())
        .filter(|path| {
            path.extension()
                .is_some_and(|candidate| candidate == extension)
        })
        .collect();
    fixtures.sort();
    fixtures
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}
