//! The corpus proposer (FZ-14; ARCHITECTURE 8.5) measured on the list-shaped stall benchmark
//! (the lock, `tests/data/lock/`) and on the maze (FZ-13).
//!
//! Two modes, as in `tests/stall_maze.rs`: the CI mode (the tests that run by default) and the
//! measurement mode (`--ignored --nocapture measure_`), which prints the lines
//! `research/stall-benchmark.md` records. Seeds 1-10 tune; seeds 11-20 are held out.

#[path = "data/bank/harness.rs"]
mod bank;
#[path = "data/lock/harness.rs"]
mod lock;
#[path = "data/maze/harness.rs"]
mod maze;
mod support;

use std::{collections::BTreeMap, fmt::Write as _, thread};

use k_rust_fuzz::{
    Campaign, CampaignError, ProposerConfig, report::CorpusParameters, spec::ProposerKind,
};
use maze::Configuration;

/// The seeds the corpus's parameters were tuned on.
const TUNING_SEEDS: [u64; 10] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

/// The held-out seeds.
const HELD_OUT_SEEDS: [u64; 10] = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20];

/// The measurement budget per cell, the stall benchmark's.
const MEASURE_BUDGET: u64 = 5000;

/// Every cell of the bank.
const BANK_CELLS: [&str; 4] = ["pay", "double", "rich", "broke"];

/// Every cell of the lock.
const LOCK_CELLS: [&str; 6] = ["l1", "l2", "l3", "l4", "l5", "lu"];

/// The CI comparison's seeds: tuning seeds, so the pins below are regression pins of the
/// corpus's case sequence, not evidence; the evidence is the measurement mode's held-out seeds.
const CI_SEEDS: [u64; 5] = [1, 2, 3, 4, 5];

/// blind+dictionary+climb on the lock at [`CI_SEEDS`] within 5000 cases (the gate
/// measurement, `research/stall-benchmark.md`, FZ-14): `l2` at none of them, `l5` never.
const GATE_LOCK_L2: [Option<u64>; 5] = [None, None, None, None, None];

/// blind+corpus's cases to the lock's last cell `l5` at [`CI_SEEDS`] within 5000 cases:
/// regression pins. They move whenever the corpus's case sequence moves (its parameters, its
/// mutations or its harvest), as `tests/golden.rs`'s corpus fingerprint does.
/// Before the run-time literals (FZ-16) they were 1094, 3452, 2546, 1310 and 1987: a key a
/// guard compared with a constant now takes the passing value from the comparison.
const PINNED_LOCK_L5: [Option<u64>; 5] = [Some(118), Some(107), Some(72), Some(62), Some(75)];

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

fn configuration(name: &'static str, weights: &[(ProposerKind, u32)]) -> Configuration {
    Configuration {
        name,
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights: weights.iter().copied().collect::<BTreeMap<_, _>>(),
        },
        target_blind: false,
    }
}

/// Blind sampling and the dictionary at equal weights (FZ-11).
fn blind_dictionary() -> Configuration {
    configuration(
        "blind+dictionary",
        &[(ProposerKind::Blind, 1), (ProposerKind::Dictionary, 1)],
    )
}

/// Blind sampling and the corpus at equal weights (FZ-14).
fn blind_corpus() -> Configuration {
    configuration(
        "blind+corpus",
        &[(ProposerKind::Blind, 1), (ProposerKind::Corpus, 1)],
    )
}

/// Blind sampling, the dictionary and the corpus at equal weights: the corpus measured against
/// blind+dictionary, so that it is not credited with the dictionary's harvest (review S2).
fn blind_dictionary_corpus() -> Configuration {
    configuration(
        "blind+dictionary+corpus",
        &[
            (ProposerKind::Blind, 1),
            (ProposerKind::Dictionary, 1),
            (ProposerKind::Corpus, 1),
        ],
    )
}

/// Every proposer of this build at equal weights.
fn blind_dictionary_climb_corpus() -> Configuration {
    configuration(
        "blind+dictionary+climb+corpus",
        &[
            (ProposerKind::Blind, 1),
            (ProposerKind::Dictionary, 1),
            (ProposerKind::Climb, 1),
            (ProposerKind::Corpus, 1),
        ],
    )
}

/// The configurations with the corpus proposer.
fn corpus_configurations() -> Vec<Configuration> {
    vec![blind_corpus(), blind_dictionary_climb_corpus()]
}

/// The maze's cells measured with the corpus: every cell but `c7` (the solver's).
const MAZE_CELLS: [&str; 15] = [
    "c1", "c2", "c3", "c4", "c5", "c6", "s1", "s2", "s3", "s4", "s5", "u1", "u2", "u3", "u4",
];

/// The configurations before the corpus proposer: the gate's evidence.
fn gate_configurations() -> Vec<Configuration> {
    vec![
        maze::blind(),
        blind_dictionary(),
        maze::blind_climb(),
        maze::blind_dictionary_climb(),
    ]
}

#[test]
fn every_reachable_lock_cell_has_a_witness_and_lu_none() {
    for cell in &lock::CELLS {
        let witness = cell.reachable().then(|| lock::keys(cell.witness));
        // Every witness of a reachable cell, as the one explicit assignment.
        for other in lock::CELLS.iter().filter(|other| other.reachable()) {
            let configuration = Configuration {
                name: "witness",
                proposers: ProposerConfig {
                    anchors_first: false,
                    explicit: vec![BTreeMap::from([(
                        "KEYS".to_owned(),
                        lock::keys(other.witness),
                    )])],
                    weights: BTreeMap::new(),
                },
                target_blind: true,
            };
            let (hit, _) = lock::run_cell(cell, &configuration, 1, 1);
            // A list fires cell k exactly when its first k keys are the corridor's: the
            // witness of a deeper cell fires every shallower one.
            let fires = witness.is_some() && other.witness.starts_with(cell.witness);
            assert_eq!(
                hit.is_some(),
                fires,
                "cell {} under {:?}",
                cell.label,
                other.witness
            );
        }
    }
    // The anchor `ListItem(0)` reaches no cell.
    let (hit, report) = lock::run_cell(lock::cell_named("l1"), &maze::blind(), 1, 1);
    assert_eq!((hit, report.totals.cases), (None, 1));
}

#[test]
fn every_reachable_bank_cell_has_a_witness_and_broke_none() {
    for cell in &bank::CELLS {
        for other in bank::CELLS.iter().filter(|other| other.reachable()) {
            let configuration = Configuration {
                name: "witness",
                proposers: ProposerConfig {
                    anchors_first: false,
                    explicit: vec![BTreeMap::from([(
                        "TXS".to_owned(),
                        bank::txs(other.witness),
                    )])],
                    weights: BTreeMap::new(),
                },
                target_blind: true,
            };
            let (hit, _) = bank::run_cell(cell, &configuration, 1, 1);
            // `pay` fires on every witness's first transaction, `double` on the third
            // transaction of `double`'s and `rich`'s, `rich` only on its own five.
            let fires = match cell.label {
                "pay" => true,
                "double" => other.witness.len() >= 3,
                "rich" => other.label == "rich",
                _ => false,
            };
            assert_eq!(
                hit.is_some(),
                fires,
                "cell {} under {}",
                cell.label,
                other.label
            );
        }
    }
    // The anchor `ListItem(tx(7, 1))` has the wrong nonce and reaches no cell.
    let (hit, report) = bank::run_cell(bank::cell_named("pay"), &maze::blind(), 1, 1);
    assert_eq!((hit, report.totals.cases), (None, 1));
}

#[test]
fn the_corpus_opens_the_lock_where_blind_sampling_the_dictionary_and_the_climb_stall() {
    let l5 = per_seed(&CI_SEEDS, |seed| {
        lock::run_cell(
            lock::cell_named("l5"),
            &blind_corpus(),
            seed,
            MEASURE_BUDGET,
        )
        .0
    });
    assert!(l5.iter().all(Option::is_some), "{l5:?}");
    assert!(GATE_LOCK_L2.iter().all(Option::is_none));
    assert_eq!(
        l5, PINNED_LOCK_L5,
        "the corpus's case sequence moved; re-pin"
    );
}

/// blind+dictionary+climb's cases to the bank's `double` at [`CI_SEEDS`] within
/// [`BANK_CI_BUDGET`] cases, with the run-time literals (FZ-16): regression pins of tuning
/// seeds. Without them no configuration reached `double` at any of seeds 1-20 within 5000 cases
/// but one (`research/stall-benchmark.md`, FZ-14 round 2 and FZ-16).
const PINNED_BANK_DOUBLE: [Option<u64>; 5] = [Some(705), Some(56), Some(155), Some(191), Some(203)];

/// The CI budget of the bank's `double`.
const BANK_CI_BUDGET: u64 = 1000;

#[test]
fn the_run_time_literals_open_the_bank_s_state_relative_cell() {
    // `double` needs an amount equal to the balance after the earlier transactions of the same
    // list: no harvest holds it, and a nudge hits it by chance. The guard `A ==Int B` compares
    // it with the balance, and the climb takes the value from the comparison.
    let double = per_seed(&CI_SEEDS, |seed| {
        bank::run_cell(
            bank::cell_named("double"),
            &maze::blind_dictionary_climb(),
            seed,
            BANK_CI_BUDGET,
        )
        .0
    });
    assert!(double.iter().all(Option::is_some), "{double:?}");
    assert_eq!(
        double, PINNED_BANK_DOUBLE,
        "the climb's case sequence moved; re-pin"
    );
}

#[test]
fn a_corpus_campaign_reports_the_same_bytes_twice_and_records_its_parameters() {
    let cell = lock::cell_named("l2");
    let (first_hit, first) = lock::run_cell(cell, &blind_corpus(), 1, 400);
    let (second_hit, second) = lock::run_cell(cell, &blind_corpus(), 1, 400);
    assert!(first_hit.is_some());
    assert_eq!(first_hit, second_hit);
    assert_eq!(first.to_canonical_json(), second.to_canonical_json());
    assert_eq!(
        first.identity.corpus,
        Some(CorpusParameters::for_target(
            &lock::spec(cell, &blind_corpus(), 1).target.kind
        ))
    );
    assert!(
        first
            .to_canonical_json()
            .contains("\"corpus\":{\"budget-share\":[1,2]")
    );
    // A campaign without the corpus records no corpus parameters.
    let (_, blind) = lock::run_cell(cell, &maze::blind(), 1, 4);
    assert_eq!(blind.identity.corpus, None);
    assert!(!blind.to_canonical_json().contains("\"corpus\":{"));
}

#[test]
fn a_corpus_weight_of_zero_changes_no_case_of_the_other_proposers() {
    // The climb's isolated window cell, as `tests/climb.rs` runs it, with and without an
    // explicit corpus weight of 0: every case and the witness are the same; the identity
    // differs only in the weights it records.
    let cell = maze::cell_named("c4");
    let without = maze::blind_dictionary_climb();
    let mut with_zero = without.clone();
    with_zero.proposers.weights.insert(ProposerKind::Corpus, 0);
    let (first_run, first) = maze::run_isolated(cell, &without, 3, 300);
    let (second_run, second) = maze::run_isolated(cell, &with_zero, 3, 300);
    assert_eq!(first_run, second_run);
    assert_eq!(first.totals, second.totals);
    assert_eq!(first.outcome, second.outcome);
    assert_eq!(second.identity.corpus, None);
    let mut identity = second.identity.clone();
    identity.proposers.weights.remove(&ProposerKind::Corpus);
    assert_eq!(identity, first.identity);
}

#[test]
fn the_corpus_needs_blind_sampling_or_the_dictionary() {
    let alone = configuration("corpus", &[(ProposerKind::Corpus, 1)]);
    let refused = Campaign::new(lock::spec(lock::cell_named("l1"), &alone, 1));
    assert!(
        matches!(&refused, Err(CampaignError::InvalidOptions { message }) if message.contains("corpus")),
        "{:?}",
        refused.err()
    );
    let with_dictionary = configuration(
        "dictionary+corpus",
        &[(ProposerKind::Dictionary, 1), (ProposerKind::Corpus, 1)],
    );
    assert!(Campaign::new(lock::spec(lock::cell_named("l1"), &with_dictionary, 1)).is_ok());
}

/// Print each configuration's lines and per-cell summaries over `seeds`.
fn measure_lock(configurations: &[Configuration], seeds: &[u64]) {
    measure_list("lock", &LOCK_CELLS, configurations, seeds, lock::run_line);
}

/// Print each configuration's lines and per-cell summaries over `seeds`, on the bank.
fn measure_bank(configurations: &[Configuration], seeds: &[u64]) {
    measure_list("bank", &BANK_CELLS, configurations, seeds, bank::run_line);
}

/// The lines of `run_line` over `cells` for each configuration and seed, then a summary line
/// per configuration, `benchmark` naming it.
fn measure_list(
    benchmark: &str,
    cells: &[&str],
    configurations: &[Configuration],
    seeds: &[u64],
    run_line: impl Fn(&Configuration, &[&str], u64, u64) -> (String, Vec<Option<u64>>) + Sync,
) {
    for configuration in configurations {
        let runs = per_seed(seeds, |seed| {
            run_line(configuration, cells, seed, MEASURE_BUDGET)
        });
        for (line, _) in &runs {
            println!("{line}");
        }
        let mut table = format!("{benchmark} {}:", configuration.name);
        for (index, label) in cells.iter().enumerate() {
            let cases: Vec<Option<u64>> = runs.iter().map(|(_, cases)| cases[index]).collect();
            write!(table, " {label} {};", lock::summary(&cases, MEASURE_BUDGET))
                .expect("writing to a String");
        }
        println!("{table}");
    }
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_gate_lock_tuning() {
    measure_lock(&gate_configurations(), &TUNING_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_gate_lock_held_out() {
    measure_lock(&gate_configurations(), &HELD_OUT_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_corpus_lock_tuning() {
    measure_lock(&corpus_configurations(), &TUNING_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_corpus_lock_held_out() {
    measure_lock(&corpus_configurations(), &HELD_OUT_SEEDS);
}

/// Print each configuration's maze lines over `seeds` (`maze::MazeRun::line`, unreached cells
/// left out) and the summary of each cell.
fn measure_maze(configurations: &[Configuration], seeds: &[u64]) {
    for configuration in configurations {
        let runs = per_seed(seeds, |seed| {
            let cells = maze::CELLS
                .iter()
                .map(|cell| {
                    if MAZE_CELLS.contains(&cell.label) {
                        maze::run_cell(cell, configuration, seed, MEASURE_BUDGET).0
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
            maze::MazeRun {
                configuration: configuration.name,
                isolated: false,
                target_blind: false,
                seed,
                budget: MEASURE_BUDGET,
                cells,
            }
        });
        for run in &runs {
            maze::check(run);
            println!("{}", run.line());
        }
        println!("{}", maze::summary(&runs));
    }
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_corpus_maze_tuning() {
    measure_maze(&corpus_configurations(), &TUNING_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_corpus_maze_held_out() {
    measure_maze(&corpus_configurations(), &HELD_OUT_SEEDS);
}

/// The configurations of round 2 on the lock and the maze: the corpus beside blind+dictionary,
/// and all four proposers again under the guided proposers' joint share.
fn round2_configurations(baseline: bool) -> Vec<Configuration> {
    let mut configurations = Vec::new();
    if baseline {
        configurations.push(blind_dictionary());
    }
    configurations.push(blind_dictionary_corpus());
    configurations.push(blind_dictionary_climb_corpus());
    configurations
}

/// Every configuration measured on the bank.
fn bank_configurations() -> Vec<Configuration> {
    vec![
        maze::blind(),
        blind_dictionary(),
        maze::blind_dictionary_climb(),
        blind_corpus(),
        blind_dictionary_corpus(),
        blind_dictionary_climb_corpus(),
    ]
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_round2_lock_tuning() {
    measure_lock(&round2_configurations(false), &TUNING_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_round2_lock_held_out() {
    measure_lock(&round2_configurations(false), &HELD_OUT_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_round2_maze_tuning() {
    measure_maze(&round2_configurations(true), &TUNING_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_round2_maze_held_out() {
    measure_maze(&round2_configurations(true), &HELD_OUT_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_bank_tuning() {
    measure_bank(&bank_configurations(), &TUNING_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_bank_held_out() {
    measure_bank(&bank_configurations(), &HELD_OUT_SEEDS);
}

/// The configurations whose cases the run-time literals change (FZ-16): those with the climb or
/// the corpus.
fn runtime_configurations() -> Vec<Configuration> {
    vec![
        maze::blind_climb(),
        maze::blind_dictionary_climb(),
        blind_corpus(),
        blind_dictionary_corpus(),
        blind_dictionary_climb_corpus(),
    ]
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_runtime_bank_tuning() {
    measure_bank(&runtime_configurations(), &TUNING_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_runtime_bank_held_out() {
    measure_bank(&runtime_configurations(), &HELD_OUT_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_runtime_maze_tuning() {
    measure_maze(&runtime_configurations(), &TUNING_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_runtime_maze_held_out() {
    measure_maze(&runtime_configurations(), &HELD_OUT_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_runtime_lock_tuning() {
    measure_lock(&runtime_configurations(), &TUNING_SEEDS);
}

#[test]
#[ignore = "measurement mode: run with --ignored --nocapture measure_"]
fn measure_runtime_lock_held_out() {
    measure_lock(&runtime_configurations(), &HELD_OUT_SEEDS);
}

/// A quick look at the bank under one configuration (`RUNTIME_PROBE` = its index in
/// [`runtime_configurations`], `RUNTIME_SEEDS` = a count of tuning seeds).
#[test]
#[ignore = "probe: run with --ignored --nocapture probe_"]
fn probe_runtime_bank() {
    let index: usize =
        std::env::var("RUNTIME_PROBE").map_or(1, |text| text.parse().expect("index"));
    let seeds: usize =
        std::env::var("RUNTIME_SEEDS").map_or(3, |text| text.parse().expect("count"));
    let configuration = runtime_configurations().swap_remove(index);
    measure_bank(&[configuration], &TUNING_SEEDS[..seeds]);
}
