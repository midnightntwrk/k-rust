//! `krs kink query` on a corpus with `[stop]` and `[observe]`.
//!
//! The fixture is a ticker that never ends on its own: its one rewrite rule `tick` turns
//! `tick(n)` into `tick(n + 1)`, and its configuration has a second cell, `ticks`, which no rule
//! changes and which the observation reads. The corpus `kink` stops after the third `tick`, names
//! the stop by its KRS item (`crate::tick`), and declares a point class before `tick`; the corpus
//! `corpora/free` has neither. Each runs the one case `tick(0)`.
//!
//! On the stopped corpus a case's states are those of the truncated system, so `tick(2)` (before
//! the stop) and `tick(3)` (at it) are hits and `tick(4)` (reachable only past it) is a `no`,
//! although the run has no end of its own; without the stop `tick(4)` is a hit. A stopped run
//! reports the depth and the state it reached, not the rewrite steps of the path to it, so the
//! witness's `rules` is `null` and the front end names no step (`krs_rules`). The query ignores
//! `[observe]`, which the document states, and the front end names the declaration and the stop
//! by the KRS spellings the corpus wrote.

#![cfg(feature = "kink")]

use std::fs;
use std::path::Path;
use std::process::Output;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const PACKAGE: &str = "krs-cli-kink-query-stop";

const LIBRARY: &str = r#"use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("tick({value})")] Tick { value: Int },
}

#[k::rule]
fn tick(k::term![ExpSyntax::Tick { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Tick(int::add(value, 1))
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub ticks: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm], ticks: 0 }
    }
}
"#;

/// The patterns: a state before the stop, the stop's state, and a state past it.
const PATTERNS: &str = "[[pattern]]\nid = \"before\"\npattern = \"<k> tick(2) </k>\"\n\n\
                        [[pattern]]\nid = \"at-stop\"\npattern = \"<k> tick(3) </k>\"\n\n\
                        [[pattern]]\nid = \"past-stop\"\npattern = \"<k> tick(4) </k>\"\n";

/// The ticker's package with its two corpora, and the fixture target `krs` builds in.
struct Package {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Package {
    fn new() -> Self {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let directory = temp_dir();
        let root = directory.path();
        let write = |relative: &str, contents: &str| {
            let path = root.join(relative);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, contents).unwrap();
        };
        write("src/lib.rs", LIBRARY);
        write(
            "Cargo.toml",
            &format!(
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"QUERY-STOP\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
                serde_json::to_string(krs.to_str().unwrap()).unwrap(),
            ),
        );
        for (corpus, sections) in [
            (
                "kink",
                "[stop]\nafter = [\"crate::tick\"]\ncount = 3\n\n[[observe.point]]\nname = \
                 \"ticks\"\nbefore = [\"crate::tick\"]\nstutter = \"count\"\ncells = [\"ticks\"]\n",
            ),
            ("corpora/free", ""),
        ] {
            // The clock never decides a run of the tests.
            write(
                &format!("{corpus}/FLOW.toml"),
                &format!(
                    "[spec]\nkrs = {{ definition = \"main\" }}\n\n[budget]\ntime_ms = 600000\n\n\
                     {sections}\n[[program]]\nid = \"t0\"\nfile = \"cases/t0.tick\"\n"
                ),
            );
            write(&format!("{corpus}/cases/t0.tick"), "tick(0)\n");
            write(&format!("{corpus}/PATTERNS.toml"), PATTERNS);
        }
        Self {
            directory,
            target: shared_fixture_target(),
        }
    }

    /// `krs kink query ARGUMENTS` on the package.
    fn query(&self, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.directory.path())
            .args(["kink", "query"])
            .args(arguments)
            .args(["--package", PACKAGE, "--definition", "main"]);
        process.output().unwrap()
    }
}

fn json_of(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

#[track_caller]
fn assert_status(output: &Output, code: i32) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The row of `pattern` (the corpus has one program).
fn row<'d>(document: &'d Value, pattern: &str) -> &'d Value {
    document["rows"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .find(|row| row["pattern"] == pattern)
        .unwrap_or_else(|| panic!("no row of {pattern}: {document:#}"))
}

/// The module documentation's answers, on both corpora.
#[test]
fn query_answers_through_the_stopped_run_and_ignores_the_observation() {
    let package = Package::new();
    let output = package.query(&[]);
    assert_status(&output, 0);
    let document = json_of(&output);
    assert_eq!(document["schema"], "kink-flow-query", "{document:#}");

    // The stop, at the K level and as the corpus wrote it.
    let stop = &document["stop"];
    let labels = stop["krs"]["items"]["crate::tick"].clone();
    assert_eq!(
        labels.as_array().map(Vec::len),
        Some(1),
        "the item names its one rewrite rule: {stop:#}"
    );
    assert_eq!(
        (&stop["before"], &stop["after"], &stop["count"]),
        (&json!([]), &labels, &json!(3)),
        "{stop:#}"
    );

    // The observation, admitted and ignored, named by the cell the corpus wrote.
    let observe = &document["observe"];
    assert!(
        observe["ignored"]
            .as_str()
            .is_some_and(|reason| reason.contains("observation channels compare two")),
        "{observe:#}"
    );
    assert_eq!(observe["declaration"]["points"][0]["name"], "ticks");
    assert_eq!(
        observe["krs"]["items"]["crate::tick"], labels,
        "{observe:#}"
    );
    assert_eq!(
        observe["krs"]["cells"],
        json!({"ticks": "ticks"}),
        "{observe:#}"
    );

    for (pattern, depth) in [("before", 2), ("at-stop", 3)] {
        let hit = row(&document, pattern);
        assert_eq!(
            (&hit["answer"], &hit["route"]),
            (&json!("hit"), &json!("stopped-run")),
            "{hit:#}"
        );
        let witness = &hit["witness"];
        assert_eq!(witness["depth"], depth, "{hit:#}");
        // A stopped run's witness names no step, so the front end names none either.
        assert_eq!(witness["rules"], Value::Null, "{hit:#}");
        assert_eq!(witness.get("krs_rules"), None, "{hit:#}");
    }
    let past = row(&document, "past-stop");
    assert_eq!(
        (&past["answer"], &past["route"]),
        (&json!("no"), &json!("stopped-run")),
        "{past:#}"
    );

    // Without the stop, the search reaches `tick(4)`, and its witness names its steps.
    let output = package.query(&["--corpus", "corpora/free"]);
    assert_status(&output, 0);
    let free = json_of(&output);
    assert_eq!(free.get("stop"), None, "{free:#}");
    assert_eq!(free.get("observe"), None, "{free:#}");
    let hit = row(&free, "past-stop");
    assert_eq!(
        (&hit["answer"], &hit["route"]),
        (&json!("hit"), &json!("search")),
        "{hit:#}"
    );
    let steps = hit["witness"]["krs_rules"]
        .as_array()
        .unwrap_or_else(|| panic!("the witness names its steps: {hit:#}"))
        .iter()
        .map(|step| step["item"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(steps, ["crate::tick"; 4], "{hit:#}");
}
