//! The solve proposer (FZ-15; ARCHITECTURE 8.6) measured on the stall benchmark (FZ-13;
//! ARCHITECTURE 11).
//!
//! The gate (`measure_solve_gate`): which blocked cells blind sampling, the dictionary and the
//! climb still fail on. The claim: the nonlinear cell `c7` (`H * I == 2021027`, `1 < H < I`),
//! which no configuration without the solver reaches within 5000 cases, is reached with it, and
//! the negative controls `u1`-`u4` stay unreached. Seeds 1-10 tuned the proposer's parameters;
//! seeds 11-20 are held out (FZ-15 report). Two modes, as in `tests/stall_maze.rs`: the CI mode
//! (the tests that run by default) and the measurement mode (`--ignored --nocapture measure_`).
//!
//! Every test but the portable build's refusal and the gate needs the `z3` feature.

#[path = "data/maze/harness.rs"]
mod maze;
mod support;

#[cfg(feature = "z3")]
use std::fmt::Write as _;
use std::{collections::BTreeMap, thread};

use k_rust_fuzz::{Campaign, ProposerConfig, spec::ProposerKind};
use maze::{CELLS, Configuration, MazeRun};

/// The measurement budget per cell, the stall benchmark's.
const MEASURE_BUDGET: u64 = 5000;

/// The seeds the solve proposer's parameters were tuned on.
const TUNING_SEEDS: [u64; 10] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

/// The held-out seeds, run once after the parameters were fixed.
#[cfg(feature = "z3")]
const HELD_OUT_SEEDS: [u64; 10] = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20];

/// The cells measured in isolation and on the whole maze: the blocked cells left after the
/// dictionary and the climb, the negative controls, and on the whole maze the cells blind
/// sampling passes in a few cases, where the solver's share is a cost.
#[cfg(feature = "z3")]
const ISOLATED_CELLS: [&str; 5] = ["c6", "c7", "s5", "u2", "u4"];
#[cfg(feature = "z3")]
const MAZE_CELLS: [&str; 12] = [
    "c1", "c2", "s1", "s2", "c5", "c6", "s5", "c7", "u1", "u2", "u3", "u4",
];

/// The CI seeds (tuning seeds) and budget.
#[cfg(feature = "z3")]
const CI_SEEDS: [u64; 5] = [1, 2, 3, 4, 5];
#[cfg(feature = "z3")]
const CI_BUDGET: u64 = 600;

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

/// Measure `configuration` on `labels` at `seeds`, printing each run's line and the summary.
fn runs(
    configuration: &Configuration,
    labels: &[&str],
    seeds: &[u64],
    isolated: bool,
) -> Vec<MazeRun> {
    let runs = per_seed(seeds, |seed| {
        some_cells(configuration, labels, seed, MEASURE_BUDGET, isolated)
    });
    for run in &runs {
        maze::check(run);
        println!("{}", run.line());
    }
    println!("{}", maze::summary(&runs));
    runs
}

/// Measure each `(configuration, baseline)` pair on `labels` at `seeds`, and print the per-seed
/// tally of the configuration against its baseline.
#[cfg(feature = "z3")]
fn measure(
    pairs: &[(Configuration, Configuration)],
    labels: &[&str],
    seeds: &[u64],
    isolated: bool,
) {
    let index_of = |label: &str| {
        CELLS
            .iter()
            .position(|cell| cell.label == label)
            .expect("a cell of the maze")
    };
    for (configuration, baseline) in pairs {
        let baseline_runs = runs(baseline, labels, seeds, isolated);
        let configuration_runs = runs(configuration, labels, seeds, isolated);
        let mut tally = format!(
            "{} against {} (wins-losses-ties):",
            configuration.name, baseline.name
        );
        for label in labels {
            let (wins, losses, ties) =
                maze::pairwise(&configuration_runs, &baseline_runs, index_of(label));
            write!(tally, " {label} {wins}-{losses}-{ties}").expect("writing to a String");
        }
        println!("{tally}");
    }
}

/// The gate of FZ-15: the blocked cells left after the dictionary (FZ-11) and the climb
/// (FZ-12), isolated (the nonlinear `c7`, the negative controls) and on the whole maze (the
/// deep corridor `c5`-`c7` and `s5`).
#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_solve_gate() {
    for configuration in [maze::blind_climb(), maze::blind_dictionary_climb()] {
        runs(&configuration, &["c7", "u2", "u4"], &TUNING_SEEDS, true);
        runs(
            &configuration,
            &["c5", "c6", "s5", "c7"],
            &TUNING_SEEDS,
            false,
        );
    }
}

#[cfg(feature = "z3")]
fn pairs() -> Vec<(Configuration, Configuration)> {
    vec![
        (maze::blind_solve(), maze::blind()),
        (
            maze::blind_dictionary_climb_solve(),
            maze::blind_dictionary_climb(),
        ),
    ]
}

#[cfg(feature = "z3")]
#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_solve_isolated_tuning() {
    measure(&pairs(), &ISOLATED_CELLS, &TUNING_SEEDS, true);
}

#[cfg(feature = "z3")]
#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_solve_isolated_held_out() {
    measure(&pairs(), &ISOLATED_CELLS, &HELD_OUT_SEEDS, true);
}

#[cfg(feature = "z3")]
#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_solve_tuning() {
    measure(&pairs(), &MAZE_CELLS, &TUNING_SEEDS, false);
}

#[cfg(feature = "z3")]
#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_solve_held_out() {
    measure(&pairs(), &MAZE_CELLS, &HELD_OUT_SEEDS, false);
}

/// The CI form of the claim: at every CI seed, `c7` is reached with the solver, isolated and on
/// the whole maze, and not without it at the same budget; and its queries on the unreachable
/// `u2` and `u4` find no path and no model.
#[cfg(feature = "z3")]
#[test]
fn the_solver_reaches_the_nonlinear_cell_and_no_unreachable_one() {
    let c7 = maze::cell_named("c7");
    let isolated = per_seed(&CI_SEEDS, |seed| {
        maze::run_isolated(c7, &maze::blind_dictionary_climb_solve(), seed, CI_BUDGET)
            .0
            .cases_to_hit
    });
    let whole = per_seed(&CI_SEEDS, |seed| {
        maze::run_cell(c7, &maze::blind_solve(), seed, CI_BUDGET)
            .0
            .cases_to_hit
    });
    let without = per_seed(&CI_SEEDS, |seed| {
        maze::run_isolated(c7, &maze::blind_dictionary_climb(), seed, CI_BUDGET)
            .0
            .cases_to_hit
    });
    // The cases are not pinned: the run toward `c7` meets feasibility queries the solver
    // leaves undecided within the case options' timeout, and its model query is decided within
    // its own timeout, so the cases rest on the clock (`totals.solve.outside-determinism`). A
    // query whose answer was unknown is asked again (`SolveParameters::max_asks`). Seeds 1-5
    // measured 32, 12, 17, 17, 57 (isolated) and 64, 65, 66, 79, 65 (whole maze).
    assert!(isolated.iter().all(Option::is_some), "{isolated:?}");
    assert!(whole.iter().all(Option::is_some), "{whole:?}");
    assert!(without.iter().all(Option::is_none), "{without:?}");
    // `u2`'s isolation leaves `D` free: a query on `c4`, its keyed predecessor, gives a
    // candidate in `c4`'s window, and the query on `u2` itself then finds no path that applies
    // it under `c4`'s guard. `u4`'s query finds no model of `C * C == 2`.
    let (run, report) =
        maze::run_isolated(maze::cell_named("u2"), &maze::blind_solve(), 1, CI_BUDGET);
    assert_eq!(run.cases_to_hit, None);
    let solve = report.totals.solve.expect("solve totals");
    assert!(solve.no_path >= 1, "u2: {solve:?}");
    let (run, report) =
        maze::run_isolated(maze::cell_named("u4"), &maze::blind_solve(), 1, CI_BUDGET);
    assert_eq!(run.cases_to_hit, None);
    let solve = report.totals.solve.expect("solve totals");
    assert!(solve.attempts > 0, "u4: {solve:?}");
    assert_eq!(solve.candidates, 0, "u4: {solve:?}");
}

/// A solving campaign records the solver's parameters and runs, and reports the same bytes
/// twice; a campaign without it records neither.
#[cfg(feature = "z3")]
#[test]
fn a_solve_campaign_reports_the_same_bytes_twice_and_records_its_runs() {
    let cell = maze::cell_named("c6");
    let (first_run, first) = maze::run_isolated(cell, &maze::blind_solve(), 1, 200);
    let (second_run, second) = maze::run_isolated(cell, &maze::blind_solve(), 1, 200);
    assert_eq!(first_run, second_run);
    assert_eq!(first.to_canonical_json(), second.to_canonical_json());
    assert!(first_run.cases_to_hit.is_some(), "{first_run:?}");
    assert_eq!(
        first.identity.solve,
        Some(k_rust_fuzz::report::SolveParameters::current())
    );
    let solve = first.totals.solve.clone().expect("solve totals");
    assert_eq!(solve.candidates, 1, "{solve:?}");
    assert_eq!(solve.outside_determinism, 0, "{solve:?}");
    // The symbolic run's work is charged to the campaign.
    assert!(first.totals.work > solve.work, "{:?}", first.totals);
    let (_, blind) = maze::run_isolated(cell, &maze::blind(), 1, 8);
    assert_eq!(blind.identity.solve, None);
    assert_eq!(blind.totals.solve, None);
    assert!(!blind.to_canonical_json().contains("\"solve\":{"));
}

/// The solver needs a generating proposer beside it and a rule target.
#[cfg(feature = "z3")]
#[test]
fn the_solver_needs_another_generating_proposer_and_a_rule_target() {
    use k_rust_fuzz::{
        Target, TargetKind,
        target::{PatternAt, PatternTarget},
    };
    let cell = maze::cell_named("c7");
    let alone = Configuration {
        name: "solve",
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights: BTreeMap::from([(ProposerKind::Solve, 1)]),
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
    let mut pattern = maze::spec(cell, &maze::blind_solve(), 1);
    pattern.target = Target {
        kind: TargetKind::Pattern(PatternTarget {
            pattern: "<k> .K </k>".into(),
            at: PatternAt::Final,
        }),
        run_to_completion: false,
        negated_property: false,
    };
    let refusal = Campaign::new(pattern).err().expect("refused").to_string();
    assert!(refusal.contains("needs a rule target"), "{refusal}");
}

/// A build without the `z3` feature refuses a positive solve weight, and names the feature.
#[cfg(not(feature = "z3"))]
#[test]
fn the_portable_build_refuses_the_solver() {
    let configuration = Configuration {
        name: "blind+solve",
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights: BTreeMap::from([(ProposerKind::Blind, 1), (ProposerKind::Solve, 1)]),
        },
        target_blind: false,
    };
    let refusal = Campaign::new(maze::spec(maze::cell_named("c7"), &configuration, 1))
        .err()
        .expect("refused")
        .to_string();
    assert!(refusal.contains("`z3` feature"), "{refusal}");
}
