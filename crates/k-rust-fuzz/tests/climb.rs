//! The climb proposer (FZ-12; ARCHITECTURE 8.4) measured on the stall benchmark (FZ-13;
//! ARCHITECTURE 11).
//!
//! The acceptance claim is the ticket's: on cells with ordered guards the cases to the first hit
//! fall against blind sampling, at the same seeds and budget. The comparison is
//! `harness::pairwise`: per seed, fewer cases wins, an unreached seed counting as more than the
//! budget.
//!
//! Seeds 1-10 tuned the climb's parameters; seeds 11-20 are held out (FZ-12 report). Two modes,
//! as in `tests/stall_maze.rs`: the CI mode (the tests that run by default) and the measurement
//! mode (`--ignored --nocapture measure_`), which prints the tables
//! `research/stall-benchmark.md` records.

#[path = "data/maze/harness.rs"]
mod maze;
mod support;

use std::{collections::BTreeMap, fmt::Write as _, thread};

use k_rust_fuzz::{
    Campaign, ProposerConfig, Target, TargetKind,
    report::ClimbParameters,
    spec::ProposerKind,
    target::{PatternAt, PatternTarget},
};
use maze::{CELLS, Configuration, MazeRun};

/// The seeds the climb's parameters were tuned on.
const TUNING_SEEDS: [u64; 10] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

/// The held-out seeds, run once after the parameters were fixed.
const HELD_OUT_SEEDS: [u64; 10] = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20];

/// The measurement budget per cell, the stall benchmark's.
const MEASURE_BUDGET: u64 = 5000;

/// The cells measured in isolation and on the whole maze: those with ordered guards (orderings,
/// windows, linear relations), and the exact and range cells as controls.
const ISOLATED_CELLS: [&str; 8] = ["c3", "c4", "c5", "c6", "s1", "s2", "s3", "s5"];
const MAZE_CELLS: [&str; 7] = ["c1", "c2", "c3", "c4", "s1", "s2", "s3"];

/// Run `measure` at every seed, one thread per seed.
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

/// A `MazeRun` of the cells `labels`, the others not run, for `harness::pairwise`.
fn some_cells(
    configuration: &Configuration,
    labels: &[&str],
    seed: u64,
    budget: u64,
    isolated: bool,
) -> MazeRun {
    let cells = CELLS
        .iter()
        .map(|cell| {
            if labels.contains(&cell.label) {
                if isolated {
                    maze::run_isolated(cell, configuration, seed, budget).0
                } else {
                    maze::run_cell(cell, configuration, seed, budget).0
                }
            } else {
                maze::CellRun {
                    cell: cell.label,
                    cases_to_hit: None,
                    cases: 0,
                    work: 0,
                }
            }
        })
        .collect();
    MazeRun {
        configuration: configuration.name,
        isolated,
        target_blind: false,
        seed,
        budget,
        cells,
    }
}

fn index_of(label: &str) -> usize {
    CELLS
        .iter()
        .position(|cell| cell.label == label)
        .expect("a cell of the maze")
}

#[test]
fn a_climb_campaign_reports_the_same_bytes_twice_and_records_its_parameters() {
    let cell = maze::cell_named("c4");
    let (first_run, first) = maze::run_isolated(cell, &maze::blind_climb(), 1, 200);
    let (second_run, second) = maze::run_isolated(cell, &maze::blind_climb(), 1, 200);
    assert_eq!(first_run, second_run);
    assert_eq!(first.to_canonical_json(), second.to_canonical_json());
    assert_eq!(first.identity.climb, Some(ClimbParameters::current()));
    assert!(
        first
            .to_canonical_json()
            .contains("\"climb\":{\"budget-share\":[1,2]")
    );
    // A campaign without the climb records no climb parameters.
    let (_, blind) = maze::run_isolated(cell, &maze::blind(), 1, 8);
    assert_eq!(blind.identity.climb, None);
    assert!(!blind.to_canonical_json().contains("\"climb\""));
}

#[test]
fn the_climb_needs_another_generating_proposer_and_a_rule_target() {
    let cell = maze::cell_named("c4");
    let alone = Configuration {
        name: "climb",
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights: BTreeMap::from([(ProposerKind::Climb, 1)]),
        },
        target_blind: false,
    };
    let refusal = Campaign::new(maze::spec(cell, &alone, 1))
        .err()
        .expect("refused")
        .to_string();
    assert!(
        refusal.contains("blind sampling or the dictionary"),
        "{refusal}"
    );
    let mut pattern = maze::spec(cell, &maze::blind_climb(), 1);
    pattern.target = Target {
        kind: TargetKind::Pattern(PatternTarget {
            pattern: "<k> .K </k>".into(),
            at: PatternAt::Final,
        }),
        run_to_completion: false,
        negated_property: false,
    };
    let refusal = Campaign::new(pattern).err().expect("refused").to_string();
    assert!(refusal.contains("rule targets only"), "{refusal}");
}

#[test]
fn the_climb_spends_at_most_half_of_the_cases() {
    // `u1` is never reached, so the campaign spends its whole budget.
    let cell = maze::cell_named("u1");
    let (_, report) = maze::run_isolated(cell, &maze::blind_climb(), 3, 120);
    assert_eq!(report.totals.cases, 120);
    // Every climb case repeats the best case's values but one or two holes; the anchors and the
    // blind cases make the rest. The report has no per-proposer count, so the share is checked
    // by the engine's unit tests; here the campaign must still run to its budget.
    assert!(report.no_witness().is_some());
}

/// Measure `configurations` beside blind on `labels` at `seeds`, and print each run's line, the
/// summary, and the per-seed pairwise tally against blind.
fn measure(configurations: &[Configuration], labels: &[&str], seeds: &[u64], isolated: bool) {
    let blind = per_seed(seeds, |seed| {
        some_cells(&maze::blind(), labels, seed, MEASURE_BUDGET, isolated)
    });
    for run in &blind {
        maze::check(run);
        println!("{}", run.line());
    }
    println!("{}", maze::summary(&blind));
    for configuration in configurations {
        let runs = per_seed(seeds, |seed| {
            some_cells(configuration, labels, seed, MEASURE_BUDGET, isolated)
        });
        for run in &runs {
            maze::check(run);
            println!("{}", run.line());
        }
        println!("{}", maze::summary(&runs));
        let mut tally = format!("{} against blind (wins-losses-ties):", configuration.name);
        for label in labels {
            let (wins, losses, ties) = maze::pairwise(&runs, &blind, index_of(label));
            write!(tally, " {label} {wins}-{losses}-{ties}").expect("writing to a String");
        }
        println!("{tally}");
    }
}

fn configurations() -> Vec<Configuration> {
    vec![maze::blind_climb(), maze::blind_dictionary_climb()]
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_climb_isolated_tuning() {
    measure(&configurations(), &ISOLATED_CELLS, &TUNING_SEEDS, true);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_climb_isolated_held_out() {
    measure(&configurations(), &ISOLATED_CELLS, &HELD_OUT_SEEDS, true);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_climb_tuning() {
    measure(&configurations(), &MAZE_CELLS, &TUNING_SEEDS, false);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_climb_held_out() {
    measure(&configurations(), &MAZE_CELLS, &HELD_OUT_SEEDS, false);
}

#[test]
#[ignore = "probe"]
fn probe_climb() {
    let runs = per_seed(&[1, 2, 3], |seed| {
        some_cells(&maze::blind_climb(), &["c4", "s3", "c6"], seed, 2000, true)
    });
    for run in &runs {
        println!("{}", run.line());
    }
}
