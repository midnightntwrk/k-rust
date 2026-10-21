//! The dictionary proposer (FZ-11; ARCHITECTURE 8.3) measured on the stall benchmark (FZ-13;
//! ARCHITECTURE 11) and run on the DICT fixture.
//!
//! The acceptance claim is the ticket's: a cell with an exact-value guard is reached in fewer
//! cases than blind sampling, at the same seeds and budget. `c3` (`C == 7`) is that cell. The
//! comparison is `harness::pairwise`: per seed, fewer cases wins, and with five seeds only five
//! wins and no loss is significant (one-sided sign test, p = 1/32).
//!
//! Two modes, as in `tests/stall_maze.rs`: the CI mode (the tests that run by default) and the
//! measurement mode (`--ignored --nocapture measure_`), which measures every cell under the
//! dictionary configurations beside blind and prints the tables `research/stall-benchmark.md`
//! records.

#[path = "data/maze/harness.rs"]
mod maze;
mod support;

use std::{collections::BTreeMap, thread};

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, OutcomeClass, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    Value,
    report::CampaignOutcome,
    spec::{DEFAULT_REJECTION_CAP, ProposerKind},
    target::{RuleMode, RuleRef, RuleTarget},
    values::{Constraints, GenerationBounds},
};
use maze::{CELLS, Configuration, MazeRun};

/// The seeds of every comparison.
const SEEDS: [u64; 5] = [1, 2, 3, 4, 5];

/// The isolated comparison's budget per cell: above blind's largest isolated `c3` count at
/// these seeds (1057, `research/stall-benchmark.md`).
const ISOLATED_BUDGET: u64 = 1100;

/// The whole-maze budget per cell, the stall benchmark's measurement budget.
const MAZE_BUDGET: u64 = 5000;

/// The measurement mode's seeds.
const MEASURE_SEEDS: [u64; 10] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

/// Blind's cases to `c3` on the whole maze at [`SEEDS`] with [`MAZE_BUDGET`]
/// (`research/stall-benchmark.md`, "First numbers"; `None` is not reached). The blind case
/// sequence is pinned by `tests/stall_maze.rs`, so a change of it fails there first; the
/// measurement mode re-runs blind beside the dictionary.
const BLIND_MAZE_C3: [Option<u64>; 5] = [None, Some(1280), Some(3468), Some(1747), None];

/// The dictionary configuration's cases to the isolated `c3` and to `c3` on the whole maze, at
/// [`SEEDS`]. They move only when the case sequence moves (the golden test's `ENGINE_VERSION`
/// fingerprint moves with it): re-pin them from the failure message.
const PINNED_ISOLATED_C3: [Option<u64>; 5] = [Some(2), Some(104), Some(19), Some(14), Some(3)];
const PINNED_MAZE_C3: [Option<u64>; 5] = [Some(288), Some(8), Some(392), Some(98), Some(56)];

/// The anchors, then blind generation and the dictionary with equal weights: the dictionary
/// beside blind, as a campaign that enables it runs.
fn dictionary() -> Configuration {
    Configuration {
        name: "blind+dictionary",
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights: BTreeMap::from([(ProposerKind::Blind, 1), (ProposerKind::Dictionary, 1)]),
        },
        target_blind: false,
    }
}

/// The anchors, then the dictionary alone (its holes that draw no harvested value draw
/// blindly).
fn dictionary_only() -> Configuration {
    Configuration {
        name: "dictionary",
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights: BTreeMap::from([(ProposerKind::Dictionary, 1)]),
        },
        target_blind: false,
    }
}

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

/// A `MazeRun` of the one cell `label`, for `harness::pairwise`.
fn one_cell(
    configuration: &Configuration,
    label: &str,
    seed: u64,
    budget: u64,
    isolated: bool,
) -> MazeRun {
    let cell = maze::cell_named(label);
    let cells = CELLS
        .iter()
        .map(|other| {
            if other.label == label {
                if isolated {
                    maze::run_isolated(cell, configuration, seed, budget).0
                } else {
                    maze::run_cell(cell, configuration, seed, budget).0
                }
            } else {
                maze::CellRun {
                    cell: other.label,
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

fn cases_to(runs: &[MazeRun], label: &str) -> Vec<Option<u64>> {
    let index = index_of(label);
    runs.iter()
        .map(|run| run.cells[index].cases_to_hit)
        .collect()
}

#[test]
fn the_dictionary_reaches_the_isolated_exact_cell_in_fewer_cases_than_blind() {
    let dictionary = per_seed(&SEEDS, |seed| {
        one_cell(&dictionary(), "c3", seed, ISOLATED_BUDGET, true)
    });
    let blind = per_seed(&SEEDS, |seed| {
        one_cell(&maze::blind(), "c3", seed, ISOLATED_BUDGET, true)
    });
    let (wins, losses, ties) = maze::pairwise(&dictionary, &blind, index_of("c3"));
    assert_eq!(
        (wins, losses, ties),
        (5, 0, 0),
        "dictionary {:?} against blind {:?}",
        cases_to(&dictionary, "c3"),
        cases_to(&blind, "c3")
    );
    assert_eq!(
        cases_to(&dictionary, "c3"),
        PINNED_ISOLATED_C3,
        "the dictionary's cases moved; re-pin them"
    );
}

#[test]
fn the_dictionary_reaches_the_exact_cell_of_the_whole_maze_in_fewer_cases_than_blind() {
    let dictionary = per_seed(&SEEDS, |seed| {
        one_cell(&dictionary(), "c3", seed, MAZE_BUDGET, false)
    });
    let ours = cases_to(&dictionary, "c3");
    for (seed, (ours, blind)) in SEEDS.iter().zip(ours.iter().zip(BLIND_MAZE_C3)) {
        let censored = |cases: Option<u64>| cases.unwrap_or(u64::MAX);
        assert!(
            ours.is_some() && censored(*ours) < censored(blind),
            "seed {seed}: dictionary {ours:?} against blind {blind:?}"
        );
    }
    assert_eq!(
        ours, PINNED_MAZE_C3,
        "the dictionary's cases moved; re-pin them"
    );
}

#[test]
fn a_dictionary_campaign_reports_the_same_bytes_twice() {
    let cell = maze::cell_named("u3");
    let (first_run, first) = maze::run_cell(cell, &dictionary(), SEEDS[0], 64);
    let (second_run, second) = maze::run_cell(cell, &dictionary(), SEEDS[0], 64);
    assert_eq!(first_run, second_run);
    assert_eq!(first.to_canonical_json(), second.to_canonical_json());
    // A second run of one campaign starts from fresh proposer state.
    let mut campaign = Campaign::new(maze::spec(cell, &dictionary(), SEEDS[0])).expect("valid");
    let again = campaign.run(Budget::Cases(64), None);
    let third = campaign.run(Budget::Cases(64), None);
    assert_eq!(again.to_canonical_json(), first.to_canonical_json());
    assert_eq!(third.to_canonical_json(), first.to_canonical_json());
}

/// The DICT campaign: holes `N` (Int) and `S` (String) of `run(3, "shut", fast)`, target
/// `goal` fired.
fn dict_spec(weights: BTreeMap<ProposerKind, u32>, seed: u64) -> CampaignSpec {
    let fixture = &support::DICT;
    let program = "dict/run.pgm";
    let hole = |name: &str, sort: &str, find: &str, literal: &str| HoleDecl {
        name: name.into(),
        sort: sort.into(),
        location: HoleLocation::Span(SpanAddress {
            program: program.into(),
            line: None,
            find: find.into(),
            literal: literal.into(),
        }),
        constraints: Constraints::default(),
        allow_refused_sort: false,
    };
    CampaignSpec {
        definitions: Definitions {
            baseline: std::sync::Arc::new(fixture.compiled().definition()),
            mutant: None,
        },
        program: ProgramInput::Source(fixture.compiled().program_source(program)),
        holes: vec![
            hole("N", "Int", "run(3,", "3"),
            hole("S", "String", "\"shut\"", "\"shut\""),
        ],
        target: Target {
            kind: TargetKind::Rule(RuleTarget {
                rule: RuleRef::Label("DICT.goal".into()),
                mode: RuleMode::Fired,
            }),
            run_to_completion: false,
            negated_property: false,
        },
        options: CaseOptions {
            shrink: false,
            ..CaseOptions::default()
        },
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights,
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed,
        identity: CallerIdentity {
            k_rust_revision: "fz26-dictionary".into(),
            thread_stack_size: None,
        },
    }
}

#[test]
fn the_dictionary_finds_a_string_and_an_equation_constant_that_blind_does_not() {
    for seed in SEEDS {
        let mut campaign = Campaign::new(dict_spec(
            BTreeMap::from([(ProposerKind::Dictionary, 1)]),
            seed,
        ))
        .expect("valid");
        let report = campaign.run(Budget::Cases(400), None);
        let CampaignOutcome::WitnessFound { witness } = &report.outcome else {
            panic!("seed {seed}: no witness: {:?}", report.outcome);
        };
        let holes: BTreeMap<&str, &Value> = witness
            .first
            .holes
            .iter()
            .map(|hole| (hole.name.as_str(), &hole.value))
            .collect();
        assert_eq!(holes["N"], &Value::Int(777.into()), "seed {seed}");
        assert_eq!(holes["S"], &Value::String("open".into()), "seed {seed}");
        assert_eq!(report.totals.classes.get(&OutcomeClass::Hit), Some(&1));
    }
    let mut blind = Campaign::new(dict_spec(
        BTreeMap::from([(ProposerKind::Blind, 1)]),
        SEEDS[0],
    ))
    .expect("valid");
    let report = blind.run(Budget::Cases(400), None);
    assert!(
        matches!(report.outcome, CampaignOutcome::NoWitnessFound { .. }),
        "{:?}",
        report.outcome
    );
}

/// Measure every cell (whole maze and isolated) under blind and the two dictionary
/// configurations, and print the tables and the pairwise comparisons against blind.
fn measure(isolated: bool) {
    let configurations = [maze::blind(), dictionary(), dictionary_only()];
    let mut all: Vec<Vec<MazeRun>> = Vec::new();
    for configuration in &configurations {
        let runs: Vec<MazeRun> = per_seed(&MEASURE_SEEDS, |seed| {
            if isolated {
                maze::run_maze_isolated(configuration, seed, MAZE_BUDGET)
            } else {
                maze::run_maze(configuration, seed, MAZE_BUDGET)
            }
        });
        for run in &runs {
            maze::check(run);
            println!("{}", run.line());
        }
        println!("{}", maze::summary(&runs));
        all.push(runs);
    }
    for (configuration, runs) in configurations.iter().zip(&all).skip(1) {
        for (index, cell) in CELLS.iter().enumerate() {
            let (wins, losses, ties) = maze::pairwise(runs, &all[0], index);
            println!(
                "{} against blind{}: {} wins={wins} losses={losses} ties={ties}",
                configuration.name,
                if isolated { " isolated" } else { "" },
                cell.label
            );
        }
    }
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_dictionary() {
    measure(false);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_dictionary_isolated() {
    measure(true);
}
