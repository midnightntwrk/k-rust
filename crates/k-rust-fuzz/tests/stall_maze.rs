//! The stall benchmark (FZ-13; ARCHITECTURE 11): the maze of `tests/data/maze`, measured as
//! the distinct cells reached and the cases to each, per proposer configuration, at fixed
//! seeds. `research/stall-benchmark.md` in the fz26 notes describes the design and records the
//! numbers; `tests/data/maze/harness.rs` holds the cells and the metric.
//!
//! Two modes, both with fixed seeds and budgets, so that both are deterministic (impl.toml
//! `[common].determinism`):
//!
//! - the CI mode, the tests that run by default: every reachable cell reached by its witness,
//!   no unreachable cell reached by any witness, the isolation of every cell, the pinned cells
//!   the blind baseline covers at a small budget, and the pinned cases to the four cells it
//!   reaches there, which must agree with the coverage;
//! - the measurement mode, `measure_blind` and `measure_blind_isolated` (ignored by default;
//!   run them with `--ignored --nocapture measure_`): one campaign per cell, over several
//!   seeds, printing the cases to each cell, on the whole maze and with each cell isolated. A
//!   proposer ticket adds its configuration to the harness and `measure_<name>` tests beside
//!   these.

#[path = "data/maze/harness.rs"]
mod maze;

use std::{collections::BTreeSet, thread};

use k_rust_fuzz::{Campaign, OutcomeClass};
use maze::{CELLS, Configuration, CoverageRun, MazeRun};

/// The CI mode's seeds and budget: one blind campaign of this many cases per seed.
const CI_SEEDS: [u64; 4] = [1, 2, 3, 4];
const CI_BUDGET: u64 = 1024;

/// The measurement mode's seeds and budget per cell.
const MEASURE_SEEDS: [u64; 5] = [1, 2, 3, 4, 5];
const MEASURE_BUDGET: u64 = 5000;

/// The cells the blind baseline covers in the CI mode, one line per seed
/// ([`CoverageRun::line`]). It changes only when the case sequence changes (generator draws,
/// the schedule; the golden test's `ENGINE_VERSION` fingerprint moves with it) or when the maze
/// changes: re-pin it from the failure message, and re-run the measurement mode for the
/// research note.
const PINNED_BLIND_COVERAGE: [&str; 4] = [
    "blind seed=1 budget=1024 cells=4: c1 c2 s1 s2",
    "blind seed=2 budget=1024 cells=3: c1 c2 s1",
    "blind seed=3 budget=1024 cells=3: c1 c2 s1",
    "blind seed=4 budget=1024 cells=4: c1 c2 s1 s2",
];

/// Run `measure` at every seed, one thread per seed. The campaigns share only the compiled
/// definition and the catalog, so the result does not depend on the scheduling of the threads.
fn per_seed<T: Send>(seeds: &[u64], measure: impl Fn(u64) -> T + Sync) -> Vec<T> {
    let measure = &measure;
    thread::scope(|scope| {
        let handles: Vec<_> = seeds
            .iter()
            .map(|&seed| scope.spawn(move || measure(seed)))
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().expect("a seed's measurement panicked"))
            .collect()
    })
}

#[test]
fn every_reachable_cell_is_reached_by_its_witness_in_one_case() {
    for cell in CELLS.iter().filter(|cell| cell.reachable()) {
        let (run, _) = maze::run_cell(cell, &maze::witness_only(cell), 0, 1);
        assert_eq!(run.cases_to_hit, Some(1), "cell {}", cell.label);
        // With shrinking on, the witness shrinks to itself.
        let mut spec = maze::spec(cell, &maze::witness_only(cell), 0);
        spec.options.shrink = true;
        let report = Campaign::new(spec)
            .expect("valid")
            .run(k_rust_fuzz::Budget::Cases(1), None);
        let witness = report.witness().expect("a witness");
        assert!(
            witness
                .shrunk
                .as_ref()
                .is_none_or(|shrunk| shrunk.holes == witness.first.holes),
            "cell {}: every witness value is the passing value nearest 0: {:?}",
            cell.label,
            witness.shrunk
        );
    }
}

#[test]
fn no_witness_of_a_reachable_cell_reaches_an_unreachable_cell() {
    let witnesses: Vec<_> = CELLS
        .iter()
        .filter(|cell| cell.reachable())
        .flat_map(|cell| maze::witness_only(cell).proposers.explicit)
        .collect();
    for cell in CELLS.iter().filter(|cell| !cell.reachable()) {
        let configuration = Configuration {
            name: "every-witness",
            proposers: k_rust_fuzz::ProposerConfig {
                anchors_first: true,
                explicit: witnesses.clone(),
                weights: std::collections::BTreeMap::new(),
            },
            target_blind: true,
        };
        let budget = u64::try_from(witnesses.len()).expect("a count") + 1;
        let (run, report) = maze::run_cell(cell, &configuration, 0, budget);
        assert_eq!(run.cases_to_hit, None, "cell {}", cell.label);
        assert_eq!(run.cases, budget, "cell {}", cell.label);
        assert_eq!(
            report.totals.classes.get(&OutcomeClass::Miss),
            Some(&budget),
            "cell {}: every walk ends cleanly",
            cell.label
        );
    }
}

#[test]
fn an_isolated_cell_fixes_exactly_its_ancestors_holes() {
    let c7 = maze::cell_named("c7");
    assert_eq!(
        maze::ancestor_holes(c7),
        BTreeSet::from(["A", "B", "C", "D", "E", "F", "G"])
    );
    assert_eq!(
        maze::ancestor_holes(maze::cell_named("c1")),
        BTreeSet::new()
    );
    assert_eq!(
        maze::ancestor_holes(maze::cell_named("s3")),
        BTreeSet::from(["A", "B"])
    );

    // `c2`'s own guard reads `A`, so `c2` is not isolated, and `u3` has no isolation.
    assert_eq!(
        maze::ancestor_holes(maze::cell_named("c2")),
        BTreeSet::new()
    );
    assert!(maze::isolation_witness(maze::cell_named("u3")).is_none());

    for cell in CELLS
        .iter()
        .filter(|cell| maze::isolation_witness(cell).is_some())
    {
        // The program's literals are distinct; the fixed holes carry the witness, the free
        // holes the free anchors.
        let program = maze::isolated_program(cell);
        let literals = program.literals();
        let distinct: BTreeSet<&str> = literals.iter().copied().collect();
        assert_eq!(distinct.len(), literals.len(), "{}", program.text);
        let fixed = maze::ancestor_holes(cell);
        let witness = maze::isolation_witness(cell).expect("an isolation");
        for ((hole, free), literal) in maze::FREE_ANCHORS.iter().zip(&literals) {
            let expected = if fixed.contains(hole) {
                witness
                    .iter()
                    .find(|(name, _)| name == hole)
                    .expect("a witness value")
                    .1
            } else {
                *free
            };
            assert_eq!(*literal, expected.to_string(), "{} {hole}", cell.label);
        }

        // The anchor case is a clean miss: no anchor gives the cell's answer away.
        let anchors = Configuration {
            name: "anchors",
            proposers: k_rust_fuzz::ProposerConfig {
                anchors_first: true,
                explicit: Vec::new(),
                weights: std::collections::BTreeMap::new(),
            },
            target_blind: true,
        };
        let report = Campaign::new(maze::isolated_spec(cell, &anchors, 0))
            .unwrap_or_else(|error| panic!("cell {}: {error}", cell.label))
            .run(k_rust_fuzz::Budget::Cases(1), None);
        assert_eq!(
            report.totals.classes.get(&OutcomeClass::Miss),
            Some(&1),
            "cell {}: the anchor case",
            cell.label
        );

        // A reachable cell's witness satisfies the choice sets and hits in one case.
        if cell.reachable() {
            let witness = maze::isolated_spec(cell, &maze::witness_only(cell), 0);
            let report = Campaign::new(witness)
                .unwrap_or_else(|error| panic!("cell {}: {error}", cell.label))
                .run(k_rust_fuzz::Budget::Cases(1), None);
            assert!(report.witness().is_some(), "cell {}", cell.label);
        }
    }

    // An explicit assignment that omits H and I keeps their anchors, which in c7's isolation
    // fail its guard (the review's S1 failure: they used to be c7's answer).
    let partial = Configuration {
        name: "partial",
        proposers: k_rust_fuzz::ProposerConfig {
            anchors_first: false,
            explicit: vec![std::collections::BTreeMap::from([(
                "E".to_owned(),
                k_rust_fuzz::Value::Int(31337.into()),
            )])],
            weights: std::collections::BTreeMap::new(),
        },
        target_blind: true,
    };
    let (run, _) = maze::run_isolated(c7, &partial, 0, 1);
    assert_eq!(run.cases_to_hit, None);

    // In c7's isolation the blind proposer draws only H and I, so every case walks through c6
    // to room r6, where the nonlinear guard stops it.
    let blind = maze::isolated_spec(c7, &maze::blind(), 1);
    let report = Campaign::new(blind)
        .expect("valid")
        .run(k_rust_fuzz::Budget::Cases(32), None);
    assert!(report.no_witness().is_some());
    assert_eq!(
        report.totals.classes.get(&OutcomeClass::Miss),
        Some(&32),
        "{:?}",
        report.totals
    );
    let covered: BTreeSet<&str> = report
        .totals
        .coverage
        .applied
        .iter()
        .filter_map(|id| maze::cell_ids().get(id).copied())
        .collect();
    assert_eq!(
        covered,
        BTreeSet::from(["c1", "c2", "c3", "c4", "c5", "c6"])
    );
}

#[test]
fn the_blind_coverage_is_pinned_and_holds_no_unreachable_cell() {
    let runs = per_seed(&CI_SEEDS, |seed| {
        maze::run_coverage(&maze::blind(), seed, CI_BUDGET)
    });
    for run in &runs {
        maze::check_coverage(run);
    }
    let lines: Vec<String> = runs.iter().map(CoverageRun::line).collect();
    assert_eq!(
        lines, PINNED_BLIND_COVERAGE,
        "the blind coverage moved; re-pin it"
    );
}

/// The cells the CI mode measures per cell: those blind reaches within [`CI_BUDGET`] at some CI
/// seed, so that a hit is pinned beside the coverage line it must agree with.
const CI_CELLS: [&str; 4] = ["c1", "c2", "s1", "s2"];

/// The cases to each of [`CI_CELLS`] per CI seed ([`MazeRun::line`] over those cells). It moves
/// with [`PINNED_BLIND_COVERAGE`].
const PINNED_BLIND_CASES: [&str; 4] = [
    "blind seed=1 budget=1024 reached=4: c1=4 c2=8 s1=118 s2=743",
    "blind seed=2 budget=1024 reached=3: c1=2 c2=6 s1=25",
    "blind seed=3 budget=1024 reached=3: c1=2 c2=3 s1=18",
    "blind seed=4 budget=1024 reached=4: c1=2 c2=24 s1=2 s2=653",
];

#[test]
fn the_blind_cases_to_each_ci_cell_are_pinned_and_agree_with_the_coverage() {
    let runs: Vec<MazeRun> = per_seed(&CI_SEEDS, |seed| {
        let cells = CI_CELLS
            .iter()
            .map(|label| maze::run_cell(maze::cell_named(label), &maze::blind(), seed, CI_BUDGET).0)
            .collect();
        MazeRun {
            configuration: "blind",
            isolated: false,
            target_blind: true,
            seed,
            budget: CI_BUDGET,
            cells,
        }
    });
    // A cell's campaign hits within the budget exactly when the coverage campaign at the same
    // seed covers it (`harness::run_coverage`: the shortcut's validity, checked).
    let coverage = per_seed(&CI_SEEDS, |seed| {
        maze::run_coverage(&maze::blind(), seed, CI_BUDGET)
    });
    for (run, covered) in runs.iter().zip(&coverage) {
        for cell in &run.cells {
            assert_eq!(
                cell.cases_to_hit.is_some(),
                covered.cells.contains(&cell.cell),
                "{} against {}",
                run.line(),
                covered.line()
            );
        }
    }
    let lines: Vec<String> = runs.iter().map(MazeRun::line).collect();
    assert_eq!(
        lines, PINNED_BLIND_CASES,
        "the blind cases moved; re-pin them"
    );
}

#[test]
fn a_cell_campaign_reports_the_same_bytes_twice() {
    let cell = maze::cell_named("u3");
    let (first_run, first) = maze::run_cell(cell, &maze::blind(), CI_SEEDS[0], 64);
    let (second_run, second) = maze::run_cell(cell, &maze::blind(), CI_SEEDS[0], 64);
    assert_eq!(first_run, second_run);
    assert_eq!(first.to_canonical_json(), second.to_canonical_json());
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_blind() {
    let runs: Vec<MazeRun> = per_seed(&MEASURE_SEEDS, |seed| {
        maze::run_maze(&maze::blind(), seed, MEASURE_BUDGET)
    });
    for run in &runs {
        maze::check(run);
        println!("{}", run.line());
    }
    println!("{}", maze::summary(&runs));
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_blind_isolated() {
    let runs: Vec<MazeRun> = per_seed(&MEASURE_SEEDS, |seed| {
        maze::run_maze_isolated(&maze::blind(), seed, MEASURE_BUDGET)
    });
    for run in &runs {
        maze::check(run);
        println!("{}", run.line());
    }
    println!("{}", maze::summary(&runs));
}
