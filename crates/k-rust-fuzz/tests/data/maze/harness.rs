//! The stall benchmark's harness (FZ-13; ARCHITECTURE 11): the maze of `maze.k`, its cells,
//! the proposer configurations measured on it, and the metric.
//!
//! The metric is, per proposer configuration and seed, the distinct cells reached within a case
//! budget and the cases to each. Every cell is measured by its own campaign whose target is the
//! cell's rule in mode `fired`, so "cases to a cell" is the `cases` total of the report that
//! found a confirmed witness for it (confirmation and shrink runs are not cases). A cell that
//! no confirmed witness reached within the budget is not reached, whatever the reason. Witnesses
//! are not shrunk (`CaseOptions::shrink` is false), so a campaign spends nothing after its hit.
//!
//! A test binary includes this file with `#[path = "data/maze/harness.rs"] mod maze;`, beside
//! `mod support;` at its root, so a proposer ticket can measure its configuration beside the
//! blind baseline. The definition is the shared fixture `support::MAZE`, compiled in-process in
//! the portable build once per test binary.

#![allow(dead_code, reason = "each test binary uses a subset of the harness")]

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    sync::{Arc, OnceLock},
};

use k_rust::backend::{Backend, BackendOptions};
use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, CompiledDefinition,
    Definitions, HoleDecl, HoleLocation, OutcomeClass, ProgramInput, ProgramSource, ProposerConfig,
    SpanAddress, Target, TargetKind, Value,
    report::{CampaignOutcome, FuzzReport, HitLabel},
    spec::{DEFAULT_REJECTION_CAP, ProgramText, ProposerKind},
    target::{RuleMode, RuleRef, RuleTarget},
    values::{Constraints, GenerationBounds},
};

/// A program of the maze: one `walk` of nine distinct integer literals, the holes' anchors.
#[derive(Clone, Debug)]
pub struct Program {
    /// The program's name in hole addresses: its file under `tests/data` for [`walk`], a
    /// generated name for an isolated program.
    pub file: String,
    pub text: String,
}

/// The benchmark's program, `walk(0, 1, 2, 3, 4, 5, 6, 7, 8)`. Its anchors fail `c1`'s guard
/// `A > 0`, so the anchor case reaches no cell.
pub fn walk() -> Program {
    Program {
        file: "maze/walk.pgm".into(),
        text: include_str!("walk.pgm").into(),
    }
}

/// The anchor of each hole that an isolated program leaves free. Each fails every guard that
/// reads the hole, given any ancestor's witness values: `A = 0` fails `c1`; `B = -100` fails
/// `c2` and `s1`; `C = 3` fails every guard of `r2`, `s3` included; `D = -3` fails `c4` and
/// `s4`; `E = 4` fails `c5`; `F = 5` and `G = 6` fail `c6` and `s5`; `H = 8` and `I = 9` fail
/// `c7`. They differ from each other and from every witness value, so the literals of an
/// isolated program are distinct, as [`holes`]'s `find` texts need.
pub const FREE_ANCHORS: [(&str, i64); 9] = [
    ("A", 0),
    ("B", -100),
    ("C", 3),
    ("D", -3),
    ("E", 4),
    ("F", 5),
    ("G", 6),
    ("H", 8),
    ("I", 9),
];

impl Program {
    /// The anchor literals, in the order of [`HOLES`].
    pub fn literals(&self) -> Vec<&str> {
        let arguments = self
            .text
            .trim_end()
            .strip_prefix("walk(")
            .and_then(|rest| rest.strip_suffix(')'))
            .unwrap_or_else(|| panic!("{} is one walk", self.file));
        let literals: Vec<&str> = arguments.split(", ").collect();
        assert_eq!(literals.len(), HOLES.len(), "{}", self.file);
        literals
    }
}

const MAIN_MODULE: &str = "MAZE";

/// What a cell's guard tests, and so which proposer is meant to crack it
/// (`research/stall-benchmark.md`, "Cells").
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GuardKind {
    /// A wide comparison with a constant: blind sampling passes it often.
    Range,
    /// A comparison or equality between two holes: blind sampling, helped by its boundary
    /// values; the climb proposer (FZ-12) by distance.
    Ordering,
    /// Equality with a constant: the dictionary proposer (FZ-11).
    Exact,
    /// A narrow interval between two constants: the dictionary proposer through the bounds
    /// plus or minus 1 to 3, the climb proposer by distance.
    Window,
    /// A linear relation between holes with a large offset, which no harvested constant
    /// satisfies alone: the climb proposer, seeded by the dictionary.
    Linear,
    /// A product of holes equal to a constant: only the solve proposer (FZ-15).
    Nonlinear,
    /// No input fires the cell (a negative control); the cell has no witness.
    Unreachable,
}

/// One cell of the maze: a rule target.
#[derive(Clone, Copy, Debug)]
pub struct Cell {
    /// The rule's label in `maze.k` (module `MAZE`).
    pub label: &'static str,
    /// The cell that produces the room this cell leaves from; `None` for room `r0` and for the
    /// room `rz` no rule produces. A walk that fires this cell fired its parent first.
    pub parent: Option<&'static str>,
    pub guard: GuardKind,
    /// The holes the cell's own guard reads.
    pub reads: &'static [&'static str],
    /// An assignment of every hole that fires the cell, each value the passing value nearest 0
    /// so that shrinking keeps no candidate; empty for an unreachable cell.
    pub witness: &'static [(&'static str, i64)],
}

impl Cell {
    /// Some input fires the cell.
    pub fn reachable(&self) -> bool {
        !self.witness.is_empty()
    }
}

/// The holes, in the order of `walk`'s arguments.
pub const HOLES: [&str; 9] = ["A", "B", "C", "D", "E", "F", "G", "H", "I"];

/// Every cell, corridor first, then the side cells, then the negative controls. Each witness
/// extends its parent's, with the holes no guard on its path reads at 0.
pub const CELLS: [Cell; 16] = [
    Cell {
        label: "c1",
        parent: None,
        guard: GuardKind::Range,
        reads: &["A"],
        witness: &[("A", 1)],
    },
    Cell {
        label: "c2",
        parent: Some("c1"),
        guard: GuardKind::Ordering,
        reads: &["A", "B"],
        witness: &[("A", 1), ("B", 2)],
    },
    Cell {
        label: "c3",
        parent: Some("c2"),
        guard: GuardKind::Exact,
        reads: &["C"],
        witness: &[("A", 1), ("B", 2), ("C", 7)],
    },
    Cell {
        label: "c4",
        parent: Some("c3"),
        guard: GuardKind::Window,
        reads: &["D"],
        witness: &[("A", 1), ("B", 2), ("C", 7), ("D", 1001)],
    },
    Cell {
        label: "c5",
        parent: Some("c4"),
        guard: GuardKind::Exact,
        reads: &["E"],
        witness: &[("A", 1), ("B", 2), ("C", 7), ("D", 1001), ("E", 31337)],
    },
    Cell {
        label: "c6",
        parent: Some("c5"),
        guard: GuardKind::Linear,
        reads: &["F", "G"],
        witness: &[
            ("A", 1),
            ("B", 2),
            ("C", 7),
            ("D", 1001),
            ("E", 31337),
            ("F", 335_001),
            ("G", 5002),
        ],
    },
    Cell {
        label: "c7",
        parent: Some("c6"),
        guard: GuardKind::Nonlinear,
        reads: &["H", "I"],
        witness: &[
            ("A", 1),
            ("B", 2),
            ("C", 7),
            ("D", 1001),
            ("E", 31337),
            ("F", 335_001),
            ("G", 5002),
            ("H", 1009),
            ("I", 2003),
        ],
    },
    Cell {
        label: "s1",
        parent: Some("c1"),
        guard: GuardKind::Range,
        reads: &["B"],
        witness: &[("A", 1), ("B", -1)],
    },
    Cell {
        label: "s2",
        parent: Some("c2"),
        guard: GuardKind::Window,
        reads: &["C"],
        witness: &[("A", 1), ("B", 2), ("C", 4097)],
    },
    Cell {
        label: "s3",
        parent: Some("c2"),
        guard: GuardKind::Ordering,
        reads: &["C", "D"],
        witness: &[("A", 1), ("B", 2), ("C", -2), ("D", -2)],
    },
    Cell {
        label: "s4",
        parent: Some("c3"),
        guard: GuardKind::Range,
        reads: &["D"],
        witness: &[("A", 1), ("B", 2), ("C", 7), ("D", -1_000_001)],
    },
    Cell {
        label: "s5",
        parent: Some("c5"),
        guard: GuardKind::Linear,
        reads: &["F", "G"],
        witness: &[
            ("A", 1),
            ("B", 2),
            ("C", 7),
            ("D", 1001),
            ("E", 31337),
            ("F", 12345),
            ("G", 0),
        ],
    },
    Cell {
        label: "u1",
        parent: Some("c1"),
        guard: GuardKind::Unreachable,
        reads: &["A"],
        witness: &[],
    },
    Cell {
        label: "u2",
        parent: Some("c4"),
        guard: GuardKind::Unreachable,
        reads: &["D"],
        witness: &[],
    },
    Cell {
        label: "u3",
        parent: None,
        guard: GuardKind::Unreachable,
        reads: &[],
        witness: &[],
    },
    Cell {
        label: "u4",
        parent: Some("c2"),
        guard: GuardKind::Unreachable,
        reads: &["C"],
        witness: &[],
    },
];

/// The cell labelled `label`.
///
/// # Panics
///
/// If the maze has no such cell.
pub fn cell_named(label: &str) -> &'static Cell {
    CELLS
        .iter()
        .find(|cell| cell.label == label)
        .unwrap_or_else(|| panic!("the maze has no cell {label}"))
}

/// The maze on `krun`'s route: `support::MAZE`, compiled with no diagnostic.
///
/// # Panics
///
/// If the maze does not load or compile, or compiles with a diagnostic.
pub fn definition() -> Arc<CompiledDefinition> {
    static DEFINITION: OnceLock<Arc<CompiledDefinition>> = OnceLock::new();
    Arc::clone(DEFINITION.get_or_init(|| Arc::new(crate::support::MAZE.compiled().definition())))
}

/// The nine `Int` holes `A` .. `I` at the literals of `program`, without constraints. Each
/// hole's `find` is its literal with the text around it up to the next separator, which occurs
/// once in a `walk` of distinct literals.
pub fn holes(program: &Program) -> Vec<HoleDecl> {
    let literals = program.literals();
    let last = literals.len() - 1;
    HOLES
        .iter()
        .zip(&literals)
        .enumerate()
        .map(|(index, (name, literal))| {
            let find = match index {
                0 => format!("walk({literal},"),
                _ if index == last => format!(" {literal})"),
                _ => format!(" {literal},"),
            };
            HoleDecl {
                name: (*name).into(),
                sort: "Int".into(),
                location: HoleLocation::Span(SpanAddress {
                    program: program.file.clone(),
                    line: None,
                    find,
                    literal: (*literal).into(),
                }),
                constraints: Constraints::default(),
                allow_refused_sort: false,
            }
        })
        .collect()
}

/// A proposer configuration measured on the maze.
#[derive(Clone, Debug)]
pub struct Configuration {
    /// The name the tables print.
    pub name: &'static str,
    pub proposers: ProposerConfig,
    /// The configuration's case sequence does not depend on the target: every weighted
    /// proposer ignores the target and the history (blind), and the explicit assignments are
    /// fixed. [`run_coverage`] requires it, and [`check`] then also requires a parent to be
    /// reached in no more cases than its child.
    pub target_blind: bool,
}

/// The blind baseline: the anchors, then blind generation only (ARCHITECTURE 8.1, 8.2), spelled
/// out so that a change of `ProposerConfig::default()` cannot change the baseline.
pub fn blind() -> Configuration {
    Configuration {
        name: "blind",
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::new(),
            weights: BTreeMap::from([(ProposerKind::Blind, 1)]),
        },
        target_blind: true,
    }
}

/// Only `cell`'s witness, without the anchors and without generation: the positive control
/// that the cell is reachable and its target is judged as a hit.
///
/// # Panics
///
/// If the cell is unreachable (it has no witness).
pub fn witness_only(cell: &Cell) -> Configuration {
    assert!(cell.reachable(), "the cell {} has no witness", cell.label);
    let mut assignment: BTreeMap<String, Value> = HOLES
        .iter()
        .map(|hole| ((*hole).to_owned(), Value::Int(0.into())))
        .collect();
    for (hole, value) in cell.witness {
        assignment.insert((*hole).to_owned(), Value::Int((*value).into()));
    }
    Configuration {
        name: "witness",
        proposers: ProposerConfig {
            anchors_first: false,
            explicit: vec![assignment],
            weights: BTreeMap::new(),
        },
        target_blind: true,
    }
}

/// The holes that the guards of `cell`'s ancestors read and the cell's own guard does not.
///
/// A hole the cell's own guard reads stays free even when an ancestor reads it too, so `c2`
/// (`B > A`, under `c1`'s `A > 0`) is not isolated: fixing `A` would turn its ordering into the
/// range `B > 1`, and its isolated campaign still has to pass `c1`.
pub fn ancestor_holes(cell: &Cell) -> BTreeSet<&'static str> {
    let mut holes = BTreeSet::new();
    let mut parent = cell.parent;
    while let Some(label) = parent {
        let ancestor = cell_named(label);
        holes.extend(ancestor.reads.iter().copied());
        parent = ancestor.parent;
    }
    for hole in cell.reads {
        holes.remove(hole);
    }
    holes
}

/// The witness values an isolation of `cell` fixes its ancestor holes to: the cell's witness,
/// or, for an unreachable cell, its parent's (the path to its room); `None` for `u3`, which has
/// no parent.
pub fn isolation_witness(cell: &Cell) -> Option<&'static [(&'static str, i64)]> {
    if cell.reachable() {
        Some(cell.witness)
    } else {
        cell.parent.map(|parent| cell_named(parent).witness)
    }
}

/// The program of `cell`'s isolation: the witness value ([`isolation_witness`]) on every hole
/// of [`ancestor_holes`], and [`FREE_ANCHORS`] on the other holes. No anchor gives the cell's
/// answer away to a proposer that reads anchors (the holes an explicit assignment omits, a seed
/// corpus, a climb that starts from the anchors), and the anchor case is a `miss`.
///
/// # Panics
///
/// If the cell has no isolation ([`isolation_witness`]).
pub fn isolated_program(cell: &Cell) -> Program {
    let witness = isolation_witness(cell)
        .unwrap_or_else(|| panic!("the cell {} has no isolation", cell.label));
    let fixed = ancestor_holes(cell);
    let literals: Vec<String> = FREE_ANCHORS
        .iter()
        .map(|(hole, free)| {
            let value = if fixed.contains(hole) {
                witness.iter().find(|(name, _)| name == hole).map_or_else(
                    || panic!("{}'s isolation witness has no {hole}", cell.label),
                    |(_, value)| *value,
                )
            } else {
                *free
            };
            value.to_string()
        })
        .collect();
    Program {
        file: format!("maze/isolated-{}.pgm", cell.label),
        text: format!("walk({})\n", literals.join(", ")),
    }
}

/// The campaign that measures `cell` in isolation: on [`isolated_program`], every hole of
/// [`ancestor_holes`] is fixed to its anchor, the witness value, by a one-value choice set, so a
/// proposer measured this way only has to pass the guard of the cell's room. The other holes
/// stay free, with anchors that fail that room's guards. A negative control is isolated on its
/// parent's witness: a proposer must then find nothing with only its room's guard to beat.
///
/// # Panics
///
/// If the cell has no isolation ([`isolation_witness`]).
pub fn isolated_spec(cell: &Cell, configuration: &Configuration, seed: u64) -> CampaignSpec {
    let program = isolated_program(cell);
    let fixed = ancestor_holes(cell);
    let literals: Vec<String> = program.literals().into_iter().map(str::to_owned).collect();
    let mut spec = spec_on(&program, cell, configuration, seed);
    for (hole, literal) in spec.holes.iter_mut().zip(literals) {
        if fixed.contains(hole.name.as_str()) {
            let value: i64 = literal.parse().expect("an integer literal");
            hole.constraints.choices = Some(vec![Value::Int(value.into())]);
        }
    }
    spec
}

/// The campaign that measures `cell` under `configuration` at `seed`, on [`walk`].
pub fn spec(cell: &Cell, configuration: &Configuration, seed: u64) -> CampaignSpec {
    spec_on(&walk(), cell, configuration, seed)
}

fn spec_on(
    program: &Program,
    cell: &Cell,
    configuration: &Configuration,
    seed: u64,
) -> CampaignSpec {
    CampaignSpec {
        definitions: Definitions {
            baseline: definition(),
            mutant: None,
        },
        program: ProgramInput::Source(ProgramSource {
            program: Some(ProgramText {
                name: program.file.clone(),
                text: program.text.clone(),
                start_sort: "Pgm".into(),
            }),
            config_vars: Vec::new(),
        }),
        holes: holes(program),
        target: Target {
            kind: TargetKind::Rule(RuleTarget {
                rule: RuleRef::Label(format!("{MAIN_MODULE}.{}", cell.label)),
                mode: RuleMode::Fired,
            }),
            run_to_completion: false,
            negated_property: false,
        },
        options: CaseOptions {
            // The metric is cases to the first confirmed hit, which shrinking does not change;
            // a blind hit's shrinking costs seconds, which would keep per-cell numbers out of CI.
            shrink: false,
            ..CaseOptions::default()
        },
        proposers: configuration.proposers.clone(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed,
        identity: CallerIdentity {
            k_rust_revision: "fz26-stall-benchmark".into(),
            thread_stack_size: None,
        },
    }
}

/// The measurement of one cell.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellRun {
    pub cell: &'static str,
    /// Cases up to and including the first case whose hit was confirmed; `None` when no
    /// confirmed witness was found within the budget.
    pub cases_to_hit: Option<u64>,
    /// Cases the campaign ran.
    pub cases: u64,
    /// Backend work over every execution, confirmation and shrinking included.
    pub work: u64,
}

/// Run the campaign that measures `cell`, and return its measurement with its report.
///
/// # Panics
///
/// If the campaign is refused, reports an engine defect, or ends other than with a witness or
/// with the budget spent: on the maze every case is a clean `miss` or a `hit`, so any other
/// ending is a defect of the benchmark or of the engine, never a measurement.
pub fn run_cell(
    cell: &'static Cell,
    configuration: &Configuration,
    seed: u64,
    budget: u64,
) -> (CellRun, FuzzReport) {
    run_spec(cell, spec(cell, configuration, seed), budget)
}

/// [`run_cell`] on the campaign of [`isolated_spec`].
///
/// # Panics
///
/// As [`run_cell`], and if the cell is unreachable.
pub fn run_isolated(
    cell: &'static Cell,
    configuration: &Configuration,
    seed: u64,
    budget: u64,
) -> (CellRun, FuzzReport) {
    run_spec(cell, isolated_spec(cell, configuration, seed), budget)
}

fn run_spec(cell: &'static Cell, spec: CampaignSpec, budget: u64) -> (CellRun, FuzzReport) {
    let mut campaign = Campaign::new(spec)
        .unwrap_or_else(|error| panic!("cell {}: the campaign is refused: {error}", cell.label));
    let report = campaign.run(Budget::Cases(budget), None);
    assert!(
        report.engine_defects.is_empty(),
        "cell {}: {:#?}",
        cell.label,
        report.engine_defects
    );
    let cases_to_hit = match &report.outcome {
        CampaignOutcome::WitnessFound { witness } => {
            assert_eq!(witness.label, HitLabel::Hit, "cell {}", cell.label);
            Some(report.totals.cases)
        }
        CampaignOutcome::NoWitnessFound { .. } => None,
        other => panic!("cell {}: the campaign ended {other:?}", cell.label),
    };
    // Every walk of the maze ends naturally, so every case is a clean `miss`, or the one `hit`
    // that ended the campaign. Any other class (a bound, `unsupported`, a rejection) or a case
    // outside the determinism contract is a defect of the benchmark or of the engine, and its
    // coverage would not mean that a cell fired.
    let hits = u64::from(cases_to_hit.is_some());
    let mut expected = BTreeMap::from([(OutcomeClass::Miss, report.totals.cases - hits)]);
    if hits == 1 {
        expected.insert(OutcomeClass::Hit, 1);
    }
    expected.retain(|_, count| *count > 0);
    assert_eq!(
        report.totals.classes, expected,
        "cell {}: every case is a clean miss or the hit",
        cell.label
    );
    assert_eq!(report.totals.outside_determinism, 0, "cell {}", cell.label);
    let run = CellRun {
        cell: cell.label,
        cases_to_hit,
        cases: report.totals.cases,
        work: report.totals.work,
    };
    (run, report)
}

/// The measurement of every cell under one configuration and seed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MazeRun {
    pub configuration: &'static str,
    /// Each cell measured in isolation ([`isolated_spec`]).
    pub isolated: bool,
    /// The configuration is target-blind and the cells were measured on one program, so a
    /// child's first hit is also a hit of its parent in the same case ([`check`]).
    pub target_blind: bool,
    pub seed: u64,
    pub budget: u64,
    /// One entry per cell, in the order of [`CELLS`].
    pub cells: Vec<CellRun>,
}

impl MazeRun {
    /// The distinct cells reached.
    pub fn reached(&self) -> usize {
        self.cells
            .iter()
            .filter(|run| run.cases_to_hit.is_some())
            .count()
    }

    /// The cases to every reached cell, in the order of [`CELLS`]: `c1=3 c2=5 ...`.
    pub fn line(&self) -> String {
        let mut line = format!(
            "{}{} seed={} budget={} reached={}:",
            self.configuration,
            if self.isolated { " isolated" } else { "" },
            self.seed,
            self.budget,
            self.reached()
        );
        for run in &self.cells {
            if let Some(cases) = run.cases_to_hit {
                write!(line, " {}={cases}", run.cell).expect("writing to a String");
            }
        }
        line
    }
}

/// The cell of each rule id of the maze's catalog (coverage records ids, not labels).
///
/// # Panics
///
/// If the catalog is not available or a cell's label is not in it exactly once.
pub fn cell_ids() -> &'static BTreeMap<String, &'static str> {
    static IDS: OnceLock<BTreeMap<String, &'static str>> = OnceLock::new();
    IDS.get_or_init(|| {
        let definition = definition();
        let BackendRoute::SourceExecution {
            execution_rewrite_order,
        } = &definition.route
        else {
            panic!("the maze is on krun's route")
        };
        let internalized = Backend::internalize_source_definition(
            &definition.kore,
            MAIN_MODULE,
            execution_rewrite_order,
        )
        .unwrap_or_else(|error| panic!("the maze: {error:?}"));
        let backend = Backend::from_internalized(internalized, BackendOptions::default())
            .unwrap_or_else(|error| panic!("the maze: {error:?}"));
        let catalog = backend
            .rule_catalog(None)
            .unwrap_or_else(|error| panic!("the maze's catalog: {error:?}"));
        let mut ids = BTreeMap::new();
        for cell in &CELLS {
            let label = format!("{MAIN_MODULE}.{}", cell.label);
            let entries: Vec<_> = catalog
                .iter()
                .filter(|entry| entry.label.as_deref() == Some(label.as_str()))
                .collect();
            assert_eq!(entries.len(), 1, "{label} in the catalog");
            ids.insert(entries[0].id.clone(), cell.label);
        }
        ids
    })
}

/// The cells some case of one campaign fired, from the report's coverage.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoverageRun {
    pub configuration: &'static str,
    pub seed: u64,
    pub budget: u64,
    /// The cells in coverage `applied`, in the order of [`CELLS`].
    pub cells: Vec<&'static str>,
}

impl CoverageRun {
    /// `blind seed=1 budget=256 cells=3: c1 c2 s1`.
    pub fn line(&self) -> String {
        format!(
            "{} seed={} budget={} cells={}: {}",
            self.configuration,
            self.seed,
            self.budget,
            self.cells.len(),
            self.cells.join(" ")
        )
    }
}

/// The cells `budget` cases of `configuration` at `seed` fire, from one campaign aimed at `u1`,
/// which no case reaches (its guard is unsatisfiable, but the rule graph reaches it, so no
/// handling of statically unreachable targets applies), so that the campaign spends its whole
/// budget and never shrinks.
///
/// This is the distinct-cells half of the metric, at the cost of one campaign, and it is valid
/// only for a target-blind configuration ([`Configuration::target_blind`]):
/// - the schedule and value RNGs are seeded from the campaign seed alone, and the blind proposer
///   ignores its context and observes nothing, so the holes, the generators and the case
///   sequence do not depend on the target;
/// - only the campaign's own target is judged, and the first confirmed hit ends a campaign, so
///   confirmation and shrinking run after its last case and draw from neither RNG;
/// - so the first `budget` cases of the `u1` campaign are those of every cell's campaign, and a
///   cell is in coverage `applied` within them exactly when its own campaign would hit within
///   them, given that every case is a clean `miss` ([`run_cell`] asserts it): a clean leaf's
///   coverage holds only rules that fired on its path.
///
/// # Panics
///
/// As [`run_cell`]; if the configuration is not target-blind; if a case is anything but a clean
/// `miss`, or the report carries a warning.
pub fn run_coverage(configuration: &Configuration, seed: u64, budget: u64) -> CoverageRun {
    assert!(
        configuration.target_blind,
        "coverage measures only a target-blind configuration, not {}",
        configuration.name
    );
    let (run, report) = run_cell(cell_named("u1"), configuration, seed, budget);
    assert_eq!(run.cases_to_hit, None, "u1 is unreachable");
    assert_eq!(
        report.totals.classes,
        BTreeMap::from([(OutcomeClass::Miss, budget)]),
        "every coverage case is a clean miss"
    );
    assert!(report.warnings.is_empty(), "{:?}", report.warnings);
    let applied: BTreeSet<&str> = report
        .totals
        .coverage
        .applied
        .iter()
        .filter_map(|id| cell_ids().get(id).copied())
        .collect();
    CoverageRun {
        configuration: configuration.name,
        seed,
        budget,
        cells: CELLS
            .iter()
            .map(|cell| cell.label)
            .filter(|label| applied.contains(label))
            .collect(),
    }
}

/// Check a coverage run: no unreachable cell, and every covered cell's parent covered.
///
/// # Panics
///
/// On a violation.
pub fn check_coverage(run: &CoverageRun) {
    for label in &run.cells {
        let cell = cell_named(label);
        assert!(
            cell.reachable(),
            "{}: the unreachable cell {label} was reached",
            run.line()
        );
        if let Some(parent) = cell.parent {
            assert!(
                run.cells.contains(&parent),
                "{}: {label} fired, its parent {parent} did not",
                run.line()
            );
        }
    }
}

/// Measure every cell under `configuration` at `seed` with a budget of `budget` cases per cell.
pub fn run_maze(configuration: &Configuration, seed: u64, budget: u64) -> MazeRun {
    MazeRun {
        configuration: configuration.name,
        isolated: false,
        target_blind: configuration.target_blind,
        seed,
        budget,
        cells: CELLS
            .iter()
            .map(|cell| run_cell(cell, configuration, seed, budget).0)
            .collect(),
    }
}

/// Measure every cell that has an isolation ([`isolated_spec`]) under `configuration` at
/// `seed`. `u3` has none and is not run: its entry is not reached, with 0 cases.
pub fn run_maze_isolated(configuration: &Configuration, seed: u64, budget: u64) -> MazeRun {
    MazeRun {
        configuration: configuration.name,
        isolated: true,
        // Each isolation has its own program and choice sets, so a child's isolated campaign
        // shares no case with its parent's.
        target_blind: false,
        seed,
        budget,
        cells: CELLS
            .iter()
            .map(|cell| {
                if isolation_witness(cell).is_some() {
                    run_isolated(cell, configuration, seed, budget).0
                } else {
                    CellRun {
                        cell: cell.label,
                        cases_to_hit: None,
                        cases: 0,
                        work: 0,
                    }
                }
            })
            .collect(),
    }
}

/// Check what every configuration must satisfy on the maze: no unreachable cell is reached,
/// and, when [`MazeRun::target_blind`], a reached cell's parent is reached in no more cases. A
/// target-directed configuration may reach a child before it reaches the parent on its own
/// campaign, so only the first property holds for it.
///
/// # Panics
///
/// On a violation.
pub fn check(run: &MazeRun) {
    let target_blind = run.target_blind;
    let by_cell: BTreeMap<&str, &CellRun> =
        run.cells.iter().map(|cell| (cell.cell, cell)).collect();
    for cell in &CELLS {
        let measured = by_cell[cell.label];
        if !cell.reachable() {
            assert_eq!(
                measured.cases_to_hit,
                None,
                "{}: the unreachable cell {} was reached",
                run.line(),
                cell.label
            );
        }
        if let (true, Some(parent), Some(cases)) =
            (target_blind, cell.parent, measured.cases_to_hit)
        {
            let parent_cases = by_cell[parent].cases_to_hit;
            assert!(
                parent_cases.is_some_and(|parent_cases| parent_cases <= cases),
                "{}: {} reached in {cases} cases, its parent {parent} in {parent_cases:?}",
                run.line(),
                cell.label
            );
        }
    }
}

/// The cases to a cell at one seed as a censored value: `None`, not reached within the budget,
/// counts as more than the budget and sorts after every number.
fn censored(cases: Option<u64>) -> (bool, u64) {
    cases.map_or((true, 0), |cases| (false, cases))
}

/// The censored median of a cell's cases over several seeds: the lower median (the element at
/// index `(n - 1) / 2` of the sorted values) with unreached seeds counted as more than the
/// budget; `None` when that median is unreached.
///
/// A configuration beats another on a cell when it reaches the cell at more seeds, or at as many
/// seeds with a lower censored median: the comparison is lexicographic on (seeds reached,
/// censored median). Over 5 seeds a one-seed difference is noise; an acceptance claim uses
/// [`pairwise`] at the same seeds.
pub fn censored_median(runs: &[MazeRun], index: usize) -> Option<u64> {
    let mut cases: Vec<(bool, u64)> = runs
        .iter()
        .map(|run| censored(run.cells[index].cases_to_hit))
        .collect();
    cases.sort_unstable();
    let (unreached, median) = cases[(cases.len() - 1) / 2];
    (!unreached).then_some(median)
}

/// Per-seed pairs of `candidate` against `baseline` on the cell at `index`: (wins, losses, ties),
/// where a win is fewer cases at the same seed, an unreached seed counting as more than the
/// budget, and two unreached seeds tie. A one-sided sign test over the wins and losses is the
/// acceptance statistic: with 5 seeds, 5 wins and no loss is significant at p = 1/32 < 0.05,
/// and anything less is not.
///
/// # Panics
///
/// If the two sets of runs differ in seeds or budget.
pub fn pairwise(candidate: &[MazeRun], baseline: &[MazeRun], index: usize) -> (u64, u64, u64) {
    assert_eq!(candidate.len(), baseline.len(), "the same seeds");
    let mut tally = (0, 0, 0);
    for (ours, theirs) in candidate.iter().zip(baseline) {
        assert_eq!(
            (ours.seed, ours.budget),
            (theirs.seed, theirs.budget),
            "the same seed and budget"
        );
        let ours = censored(ours.cells[index].cases_to_hit);
        let theirs = censored(theirs.cells[index].cases_to_hit);
        match ours.cmp(&theirs) {
            std::cmp::Ordering::Less => tally.0 += 1,
            std::cmp::Ordering::Greater => tally.1 += 1,
            std::cmp::Ordering::Equal => tally.2 += 1,
        }
    }
    tally
}

/// A table over several seeds of one configuration: per cell, the seeds that reached it first,
/// then the censored lower median ([`censored_median`], `>budget` when it is unreached), then
/// the least and greatest cases over the seeds that reached it. A cell that no seed ran (`u3`
/// in isolation) reads `not run`.
pub fn summary(runs: &[MazeRun]) -> String {
    let mut table = String::new();
    let Some(first) = runs.first() else {
        return table;
    };
    writeln!(
        table,
        "configuration {}{} budget {} seeds {:?}",
        first.configuration,
        if first.isolated { " isolated" } else { "" },
        first.budget,
        runs.iter().map(|run| run.seed).collect::<Vec<_>>()
    )
    .expect("writing to a String");
    writeln!(
        table,
        "cell  guard        reached  median (censored, lower)  min  max"
    )
    .expect("writing to a String");
    for (index, cell) in CELLS.iter().enumerate() {
        let guard = format!("{:?}", cell.guard);
        if runs.iter().all(|run| run.cells[index].cases == 0) {
            writeln!(table, "{:<5} {guard:<12} not run", cell.label).expect("writing to a String");
            continue;
        }
        let mut cases: Vec<u64> = runs
            .iter()
            .filter_map(|run| run.cells[index].cases_to_hit)
            .collect();
        cases.sort_unstable();
        let median = censored_median(runs, index)
            .map_or_else(|| format!(">{}", first.budget), |median| median.to_string());
        let range = match (cases.first(), cases.last()) {
            (Some(min), Some(max)) => format!("{min}  {max}"),
            _ => "-".to_owned(),
        };
        writeln!(
            table,
            "{:<5} {guard:<12} {}/{}  {median}  {range}",
            cell.label,
            cases.len(),
            runs.len()
        )
        .expect("writing to a String");
    }
    let reached: Vec<usize> = runs.iter().map(MazeRun::reached).collect();
    writeln!(table, "distinct cells reached per seed: {reached:?}").expect("writing to a String");
    table
}
