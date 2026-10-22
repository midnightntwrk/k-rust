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
const ISOLATED_CELLS: [&str; 11] = [
    "c3", "c4", "c5", "c6", "s1", "s2", "s3", "s5", "u1", "u2", "u4",
];
const MAZE_CELLS: [&str; 15] = [
    "c1", "c2", "c3", "c4", "c5", "c6", "s1", "s2", "s3", "s4", "s5", "u1", "u2", "u3", "u4",
];

/// The CI comparison's seeds: tuning seeds, so the pins below are regression pins of the
/// climb's case sequence, not evidence; the evidence is the measurement mode's held-out seeds.
const CI_SEEDS: [u64; 5] = [1, 2, 3, 4, 5];

/// The CI comparison's budget per cell.
const CI_BUDGET: u64 = 2000;

/// Blind's cases at [`CI_SEEDS`] (`research/stall-benchmark.md`, "First numbers"; `None`: not
/// reached within 5000 cases): the isolated window `c4` and ordering `s3`; the isolated linear
/// `c6` and the whole maze's `c4` are never reached.
const BLIND_ISOLATED_C4: [Option<u64>; 5] =
    [Some(2006), Some(1306), Some(254), Some(217), Some(290)];
const BLIND_ISOLATED_S3: [Option<u64>; 5] =
    [Some(369), Some(1730), Some(1689), Some(982), Some(3302)];

/// Blind sampling and the climb's cases at [`CI_SEEDS`] with [`CI_BUDGET`]: regression pins.
/// They move whenever the climb's case sequence moves (its parameters, moves, the score or the
/// condition records it reads), as `tests/golden.rs`'s climb fingerprint does.
const PINNED_ISOLATED_C4: [Option<u64>; 5] = [Some(50), Some(75), Some(151), Some(83), Some(65)];
const PINNED_ISOLATED_S3: [Option<u64>; 5] = [Some(47), Some(193), Some(175), Some(213), Some(141)];
const PINNED_ISOLATED_C6: [Option<u64>; 5] =
    [Some(781), Some(188), Some(239), Some(456), Some(252)];
const PINNED_MAZE_C4: [Option<u64>; 5] = [Some(921), Some(286), Some(411), Some(484), Some(934)];

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
fn the_climb_reaches_ordered_cells_in_fewer_cases_than_blind() {
    let isolated = |label: &'static str| {
        per_seed(&CI_SEEDS, |seed| {
            maze::run_isolated(
                maze::cell_named(label),
                &maze::blind_climb(),
                seed,
                CI_BUDGET,
            )
            .0
            .cases_to_hit
        })
    };
    let c4 = isolated("c4");
    let s3 = isolated("s3");
    let c6 = isolated("c6");
    let maze_c4 = per_seed(&CI_SEEDS, |seed| {
        maze::run_cell(
            maze::cell_named("c4"),
            &maze::blind_climb(),
            seed,
            CI_BUDGET,
        )
        .0
        .cases_to_hit
    });
    // Fewer cases than blind at every seed, and cells blind never reaches, reached at every one.
    let fewer = |climb: &[Option<u64>], blind: &[Option<u64>]| {
        climb.iter().zip(blind).all(|(climb, blind)| {
            climb.is_some_and(|climb| blind.is_none_or(|blind| climb < blind))
        })
    };
    assert!(fewer(&c4, &BLIND_ISOLATED_C4), "{c4:?}");
    assert!(fewer(&s3, &BLIND_ISOLATED_S3), "{s3:?}");
    assert!(c6.iter().all(Option::is_some), "{c6:?}");
    assert!(maze_c4.iter().all(Option::is_some), "{maze_c4:?}");
    assert_eq!(
        (c4, s3, c6, maze_c4),
        (
            PINNED_ISOLATED_C4.to_vec(),
            PINNED_ISOLATED_S3.to_vec(),
            PINNED_ISOLATED_C6.to_vec(),
            PINNED_MAZE_C4.to_vec()
        ),
        "the climb's case sequence moved; re-pin"
    );
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
