//! Alpha-invariance: a sentence and any renaming of its variables that keeps sigils, `_`
//! prefixes and the fixed names `HOLE`, `HERE` and `#Configuration` compile to alpha-equivalent
//! KORE and give the same `krun` answers.
//!
//! # The binding rule
//!
//! After anonymous resolution, anonymity never affects binding: `#Exists V . P` and
//! `#Forall V . P` bind exactly `V`, with ordinary lexical scope, and every other variable of a
//! rule, context, context alias or macro rule is bound by the sentence. Each `_` is its own
//! variable. A renaming that respects this rule is an alpha-renaming, and the meaning of a
//! definition cannot depend on it; so every difference this harness reports is a defect of the
//! compiler, whichever of the two spellings it gets wrong.
//!
//! # What a case is
//!
//! A case is one definition: a corpus entry (`alpha_invariance/corpus.rs`), a defect probe
//! (`probes.rs`) or a generated definition (`generate.rs`). The harness loads it once, then for
//! each renaming strategy (`rename.rs`) renames every sentence in the case's scope on the parsed
//! definition and relinks it (`LoadedDefinition::with_definition`), so the base and the variant
//! share every parsing decision. It compiles both through the library route of `kcompile`,
//! compares the compiled `definition.kore` and macros' KORE in alpha-normal form (`kore_alpha.rs`), each
//! sentence's `UNIQUE_ID` on its own, and the leaves of every program the case runs through the
//! backend's `execute`, from the initial configuration `krun` assembles (`--io off`, standard
//! input empty). A refused base must be refused by every variant with the same error codes at the
//! same lines; a panic (a kompile invariant of the test profile) is never a pass.
//!
//! # Expected failures
//!
//! `EXPECTED` (`alpha_invariance/expected.rs`) lists every result that fails today, each with
//! the ticket whose fix makes it pass, the kind of failure and a text its report must hold. A
//! listed result must still fail in that way, and an unlisted one must pass: a fix shows as
//! entries leaving the list, and a new failure (or a known one failing differently) fails the
//! test until it is listed. A reviewer's binding finding becomes a new axis of `generate.rs` or a
//! new probe, and its failing results become entries there.
//!
//! # Running
//!
//! `cargo test --test alpha_invariance` runs the probes, the prelude, the manifest's runnable
//! workspace cases and a sample of the generated grammar. The ignored tests (the whole corpus,
//! with the reference checkouts when present and every tracked K file, and the whole generated
//! grammar) are run by the `alpha-invariance` gate (`scripts/alpha-invariance.sh`).
//! `ALPHA_INVARIANCE_JOBS` sets the number of worker threads (default: up to 4), and
//! `ALPHA_INVARIANCE_OUT=<directory>` writes one line per result to `<directory>/<test>.tsv`.

#[path = "alpha_invariance/corpus.rs"]
mod corpus;
#[path = "alpha_invariance/expected.rs"]
mod expected;
#[path = "alpha_invariance/generate.rs"]
mod generate;
#[path = "alpha_invariance/harness.rs"]
mod harness;
#[path = "alpha_invariance/kore_alpha.rs"]
mod kore_alpha;
#[path = "alpha_invariance/probes.rs"]
mod probes;
#[path = "alpha_invariance/rename.rs"]
mod rename;

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    fmt::Write as _,
    fs,
    sync::{
        Mutex,
        atomic::{AtomicUsize, Ordering},
    },
    thread,
};

use expected::EXPECTED;
use harness::{Case, CaseOutcome, Failure, check, describe};
use rename::Strategy;

/// Check `cases` on every worker thread and return each one's outcome, in order.
fn run_all(cases: &[Case]) -> Vec<CaseOutcome> {
    let jobs = env::var("ALPHA_INVARIANCE_JOBS")
        .ok()
        .and_then(|jobs| jobs.parse().ok())
        .unwrap_or_else(|| {
            thread::available_parallelism()
                .map_or(1, usize::from)
                .min(4)
        })
        .max(1);
    let next = AtomicUsize::new(0);
    let outcomes: Mutex<BTreeMap<usize, CaseOutcome>> = Mutex::new(BTreeMap::new());
    thread::scope(|scope| {
        for _ in 0..jobs.min(cases.len()) {
            thread::Builder::new()
                .stack_size(256 << 20)
                .spawn_scoped(scope, || {
                    loop {
                        let index = next.fetch_add(1, Ordering::SeqCst);
                        let Some(case) = cases.get(index) else {
                            break;
                        };
                        let outcome = check(case, &Strategy::ALL);
                        outcomes.lock().unwrap().insert(index, outcome);
                    }
                })
                .expect("a worker thread starts");
        }
    });
    outcomes.into_inner().unwrap().into_values().collect()
}

/// Check `cases` against `EXPECTED` and fail with every mismatch.
fn assert_cases(test: &str, cases: Vec<Case>) {
    let mut names = BTreeSet::new();
    for case in &cases {
        assert!(
            names.insert(case.name.clone()),
            "two cases named {}",
            case.name
        );
    }
    let outcomes = run_all(&cases);
    let mut results: BTreeMap<String, Option<Failure>> = BTreeMap::new();
    for (case, outcome) in cases.iter().zip(&outcomes) {
        results.extend(describe(&case.name, outcome));
    }
    let mut mismatches = Vec::new();
    let mut table = String::new();
    let mut listing = String::new();
    for (key, failure) in &results {
        let expected = EXPECTED.iter().find(|entry| entry.key() == *key);
        let _ = writeln!(
            table,
            "{key}\t{}\t{}",
            failure
                .as_ref()
                .map_or("pass".to_owned(), |failure| format!("{:?}", failure.kind)),
            failure
                .as_ref()
                .map_or(String::new(), |failure| failure.report.replace('\n', " ")),
        );
        if let Some(failure) = failure {
            let (case, strategy) = key.split_once(' ').unwrap();
            let ticket = expected.map_or("?", |entry| entry.ticket);
            let _ = writeln!(
                listing,
                "    expected(\"{case}\", \"{strategy}\", \"{ticket}\", Kind::{:?}, \"\"),",
                failure.kind
            );
        }
        match (expected, failure) {
            (None, None) => {}
            (None, Some(failure)) => mismatches.push(format!(
                "{key}: fails and is not listed ({:?}): {}",
                failure.kind, failure.report
            )),
            (Some(entry), None) => mismatches.push(format!(
                "{key}: passes, but is listed as failing until {}: remove its entry",
                entry.ticket
            )),
            (Some(entry), Some(failure)) => {
                if failure.kind != entry.kind || !failure.report.contains(entry.needle) {
                    mismatches.push(format!(
                        "{key}: listed as {:?} holding {:?} (until {}), and fails as {:?}: {}",
                        entry.kind, entry.needle, entry.ticket, failure.kind, failure.report
                    ));
                }
            }
        }
    }
    // An entry for a case this test ran must name a result the case gave.
    for entry in EXPECTED {
        if names.contains(entry.case) && !results.contains_key(&entry.key()) {
            mismatches.push(format!(
                "{}: listed (until {}), and the case gives no such result",
                entry.key(),
                entry.ticket
            ));
        }
    }
    if let Some(directory) = env::var_os("ALPHA_INVARIANCE_OUT") {
        let directory = std::path::PathBuf::from(directory);
        fs::create_dir_all(&directory).expect("the output directory is created");
        fs::write(directory.join(format!("{test}.tsv")), &table).expect("the table is written");
    }
    let failing = results.values().filter(|failure| failure.is_some()).count();
    let left_out = outcomes
        .iter()
        .filter(|outcome| matches!(&outcome.base, Ok(summary) if summary.contains("left out")))
        .count();
    eprintln!(
        "{test}: {} cases ({left_out} left out: they do not load), {} results, {failing} failing",
        cases.len(),
        results.len()
    );
    assert!(
        mismatches.is_empty(),
        "{} mismatches with EXPECTED:\n{}\n\nevery failing result of this run:\n{listing}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

#[test]
fn every_defect_probe_is_alpha_invariant_or_listed() {
    assert_cases("probes", probes::probes());
}

#[test]
fn the_prelude_is_alpha_invariant_or_listed() {
    assert_cases("prelude", vec![corpus::prelude_case()]);
}

/// The manifest's runnable cases whose sources are in the workspace.
#[test]
fn the_runnable_workspace_corpus_is_alpha_invariant_or_listed() {
    let cases = corpus::manifest_cases(true)
        .into_iter()
        .filter(|case| !case.programs.is_empty())
        .collect();
    assert_cases("corpus-runnable", cases);
}

/// The generated cases a sample keeps: the first of each family and every sixth after it.
fn sample(cases: Vec<Case>) -> Vec<Case> {
    let mut seen = BTreeMap::<String, usize>::new();
    cases
        .into_iter()
        .filter(|case| {
            let family = case.name.split('/').next().unwrap_or("").to_owned();
            let index = seen.entry(family).or_default();
            *index += 1;
            (*index - 1).is_multiple_of(6)
        })
        .collect()
}

#[test]
fn a_sample_of_the_generated_grammar_is_alpha_invariant_or_listed() {
    assert_cases("generated-sample", sample(generate::cases()));
}

#[test]
#[ignore = "the whole corpus: scripts/alpha-invariance.sh"]
fn the_whole_corpus_is_alpha_invariant_or_listed() {
    let mut cases = corpus::manifest_cases(false);
    let fixtures = corpus::fixture_cases(&cases);
    cases.extend(fixtures);
    assert_cases("corpus", cases);
}

#[test]
#[ignore = "the whole generated grammar: scripts/alpha-invariance.sh"]
fn the_whole_generated_grammar_is_alpha_invariant_or_listed() {
    assert_cases("generated", generate::cases());
}
