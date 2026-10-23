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

use k_rust::kore::ast::Pattern as KorePattern;
use k_rust_fuzz::{
    Budget, Campaign, ProgramInput, ProgramSource, ProposerConfig, Target, TargetKind, Value,
    report::ClimbParameters,
    spec::{ProgramText, ProposerKind},
    target::{
        ConfigurationView, Observer, ObserverTarget, ObserverVerdict, PatternAt, PatternTarget,
    },
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
/// condition records it reads), as `tests/golden.rs`'s climb fingerprint does. The run-time
/// literals (FZ-16) moved them from `c4` 50, 75, 151, 83, 65; `s3` 47, 193, 175, 213, 141;
/// `c6` 781, 188, 239, 456, 252; whole-maze `c4` 921, 286, 411, 484, 934: a window's bound or
/// `D ==Int C` gives the passing value at once, while `c6` (`3F ==Int G +Int 1000001`) compares
/// no hole's value as it is. FZ-16's fix round (only atoms below refuting nodes, a change drawn
/// by side of a comparison, none proposed twice by the climb) moved them again, from `c4` 12, 3,
/// 4, 6, 10; `s3` 12, 3, 11, 6, 10; `c6` 681, 288, 239, 410, 418; whole-maze `c4` 227, 46, 67,
/// 40, 74, by drawing the random streams differently; the isolated medians at seeds 11-20 are
/// in `exp/fz16/` of the fz26 notes (`climb-iso-*.log`).
const PINNED_ISOLATED_C4: [Option<u64>; 5] = [Some(23), Some(12), Some(35), Some(19), Some(26)];
const PINNED_ISOLATED_S3: [Option<u64>; 5] = [Some(68), Some(12), Some(11), Some(24), Some(23)];
const PINNED_ISOLATED_C6: [Option<u64>; 5] =
    [Some(693), Some(248), Some(312), Some(414), Some(316)];
const PINNED_MAZE_C4: [Option<u64>; 5] = [Some(32), Some(33), Some(77), Some(83), Some(85)];

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
    let target = maze::isolated_spec(cell, &maze::blind_climb(), 1)
        .target
        .kind;
    let parameters = ClimbParameters::for_target(&target);
    assert_eq!(parameters.condition_rules, "target-and-keyed-predecessors");
    assert_eq!(first.identity.climb, Some(parameters));
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
        data_end: true,
    };
    let refusal = Campaign::new(pattern).err().expect("refused").to_string();
    assert!(
        refusal.contains("rule and observer targets only"),
        "{refusal}"
    );
}

#[test]
fn a_climbing_campaign_runs_to_its_budget() {
    // `u1` is never reached, so the campaign spends its whole budget. The report has no
    // per-proposer count: the climb's share of the cases and of the work is checked with the
    // climb proposer itself in the engine's unit tests
    // (`the_climb_spends_at_most_half_of_the_cases_and_of_the_work`).
    let cell = maze::cell_named("u1");
    let (_, report) = maze::run_isolated(cell, &maze::blind_climb(), 3, 120);
    assert_eq!(report.totals.cases, 120);
    assert!(report.no_witness().is_some());
}

/// Accepts the step after which the maze's `<d>` cell holds `goal`, and reports as progress how
/// near `<d>` is to it otherwise (`u32::MAX` minus the gap).
struct DNear {
    goal: i64,
}

impl Observer for DNear {
    type State = ();

    fn start(&self) {}

    fn branch(&self, (): &()) {}

    fn step(
        &self,
        (): &mut (),
        _pre: &ConfigurationView,
        post: &ConfigurationView,
    ) -> ObserverVerdict {
        let mut value = None;
        let mut work: Vec<&KorePattern> = post.cell("d").into_iter().collect();
        while let Some(next) = work.pop() {
            if let KorePattern::DomainValue { value: text, .. } = next {
                value = text
                    .as_utf8()
                    .ok()
                    .and_then(|text| text.parse::<i64>().ok());
            }
            work.extend(k_rust::kore::walk::children(next));
        }
        match value {
            Some(d) if d == self.goal => ObserverVerdict::Hit,
            Some(d) => {
                let gap = u32::try_from(d.abs_diff(self.goal)).unwrap_or(u32::MAX);
                ObserverVerdict::Progress(u32::MAX - gap)
            }
            None => ObserverVerdict::Nothing,
        }
    }
}

/// An observer target climbs on the observer's progress (ARCHITECTURE 6.4): the maze's `D`
/// equal to 4242, which only the observer states, is found by blind sampling and the climb,
/// and not by blind sampling alone in the same budget.
#[test]
fn an_observer_target_climbs_on_the_observers_progress() {
    let text = "walk(1, 2, 7, -3, 4, 5, 6, 8, 9)\n";
    let program = maze::Program {
        file: "maze/observer.pgm".into(),
        text: text.into(),
    };
    let campaign = |configuration: &Configuration, seed| {
        let mut spec = maze::spec(maze::cell_named("c4"), configuration, seed);
        spec.program = ProgramInput::Source(ProgramSource {
            program: Some(ProgramText {
                name: program.file.clone(),
                text: text.into(),
                start_sort: "Pgm".into(),
            }),
            config_vars: Vec::new(),
        });
        spec.holes = maze::holes(&program);
        spec.target = Target {
            kind: TargetKind::Observer(ObserverTarget::new("d-near", DNear { goal: 4242 })),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
        };
        Campaign::new(spec)
            .expect("an observer campaign with the climb is valid")
            .run(Budget::Cases(OBSERVER_BUDGET), None)
    };
    for seed in [1, 2, 3] {
        let report = campaign(&maze::blind_climb(), seed);
        let witness = report
            .witness()
            .unwrap_or_else(|| panic!("seed {seed}: {:?}", report.totals));
        let d = witness
            .first
            .holes
            .iter()
            .find(|hole| hole.name == "D")
            .expect("the hole D");
        assert_eq!(d.value, Value::Int(4242.into()), "seed {seed}");
        // The observer's score reads no condition records, and the identity says so.
        let parameters = ClimbParameters::for_target(&TargetKind::Observer(ObserverTarget::new(
            "d-near",
            DNear { goal: 4242 },
        )));
        assert_eq!(parameters.condition_rules, "none");
        assert_eq!(report.identity.climb, Some(parameters));
        println!("seed {seed}: {} cases", report.totals.cases);
    }
    let blind = campaign(&maze::blind(), 1);
    assert!(blind.no_witness().is_some(), "blind found 4242");
}

/// The observer campaign's budget: enough for the climb at seeds 1-3 (it reaches 4242 in a few
/// hundred cases), far below what blind sampling needs to draw one exact 64-bit value.
const OBSERVER_BUDGET: u64 = 3000;

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
