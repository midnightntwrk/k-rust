//! The stall benchmark's harness (FZ-13; ARCHITECTURE 11): the maze of `maze.k`, its cells,
//! the proposer configurations measured on it, and the metric.
//!
//! The metric is, per proposer configuration and seed, the distinct cells reached within a case
//! budget and the cases to each. Every cell is measured by its own campaign whose target is the
//! cell's rule in mode `fired`, so "cases to a cell" is the `cases` total of the report that
//! found a confirmed witness for it (confirmation and shrink runs are not cases). A cell that
//! no confirmed witness reached within the budget is not reached, whatever the reason.
//!
//! A test binary includes this file with `#[path = "data/maze/harness.rs"] mod maze;`, so a
//! proposer ticket can measure its configuration beside the blind baseline. The definition is
//! compiled in-process in the portable build, exactly as `tests/support` compiles the shared
//! fixtures, once per test binary.

#![allow(dead_code, reason = "each test binary uses a subset of the harness")]

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    sync::{Arc, OnceLock},
};

use k_rust::{
    backend::{Backend, BackendOptions},
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, CompiledDefinition,
    Definitions, HoleDecl, HoleLocation, ProgramInput, ProgramSource, ProposerConfig, SpanAddress,
    Target, TargetKind, Value,
    report::{CampaignOutcome, FuzzReport, HitLabel},
    spec::{DEFAULT_REJECTION_CAP, ProgramText},
    target::{RuleMode, RuleRef, RuleTarget},
    values::{Constraints, GenerationBounds},
};

/// The definition's file under `tests/data`, which is also its source name.
pub const DEFINITION_FILE: &str = "maze/maze.k";
const SOURCE: &str = include_str!("maze.k");

/// A program of the maze: one `walk` of nine integer literals, the holes' anchors.
#[derive(Clone, Copy, Debug)]
pub struct Program {
    /// The file under `tests/data`, which is also the program's name in hole addresses.
    pub file: &'static str,
    pub text: &'static str,
}

/// The benchmark's program, `walk(0, 1, 2, 3, 4, 5, 6, 7, 8)`. Its anchors fail `c1`'s guard
/// `A > 0`, so the anchor case reaches no cell.
pub const WALK: Program = Program {
    file: "maze/walk.pgm",
    text: include_str!("walk.pgm"),
};

/// The program of the isolated mode: its anchors are `c7`'s witness, which extends the
/// witness of every corridor cell, so they satisfy the choice sets [`isolated_spec`] puts on
/// any cell's ancestor holes.
pub const DEEP: Program = Program {
    file: "maze/deep.pgm",
    text: include_str!("deep.pgm"),
};

impl Program {
    /// The anchor literals, in the order of [`HOLES`].
    pub fn literals(&self) -> Vec<&'static str> {
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
    /// A comparison between two holes.
    Ordering,
    /// Equality with a constant: the dictionary proposer (FZ-11).
    Exact,
    /// A narrow interval, or a linear relation between holes: the climb proposer (FZ-12).
    Climb,
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
        guard: GuardKind::Climb,
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
        guard: GuardKind::Climb,
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
        guard: GuardKind::Climb,
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
        guard: GuardKind::Climb,
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

/// The maze compiled in-process, as `tests/support` compiles the shared fixtures: loaded with
/// the embedded prelude and the Rust backend's load options, compiled with no diagnostic, on
/// `krun`'s route.
///
/// # Panics
///
/// If the maze does not load or compile, or compiles with a diagnostic.
pub fn definition() -> Arc<CompiledDefinition> {
    static DEFINITION: OnceLock<Arc<CompiledDefinition>> = OnceLock::new();
    Arc::clone(DEFINITION.get_or_init(|| {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let options = LoadOptions {
            implicit_sources: vec![embedded("prelude.md").expect("the prelude is embedded")],
            ..CompilationBackend::Rust.load_options()
        };
        let (loaded, syntax_module) = load_for_compilation(
            ResolvedSource::new(DEFINITION_FILE, SOURCE),
            MAIN_MODULE,
            None,
            &mut resolver,
            &options,
        )
        .unwrap_or_else(|error| panic!("the maze does not load: {error:?}"));
        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
            .unwrap_or_else(|error| {
                panic!(
                    "the maze does not compile: {error}: {:#?}",
                    error.diagnostics
                )
            });
        assert!(
            artifacts.diagnostics.is_empty(),
            "the maze compiles with diagnostics: {:#?}",
            artifacts.diagnostics
        );
        let definition = CompiledDefinition::from_artifacts(
            MAIN_MODULE,
            syntax_module,
            loaded.into_definition(),
            artifacts,
        )
        .unwrap_or_else(|error| panic!("the maze: {error:?}"));
        Arc::new(definition)
    }))
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
                    program: program.file.into(),
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
}

/// The blind baseline: the anchors, then blind generation only (ARCHITECTURE 8.1, 8.2).
pub fn blind() -> Configuration {
    Configuration {
        name: "blind",
        proposers: ProposerConfig::default(),
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
    }
}

/// The holes that the guards of `cell`'s ancestors read and the cell's own guard does not.
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

/// The campaign that measures `cell` in isolation: on [`DEEP`], every hole of
/// [`ancestor_holes`] is fixed to its anchor, the cell's witness value, by a one-value choice
/// set, so a proposer measured this way only has to pass the cell's own guard; the other holes
/// stay free. The anchor case is skipped, since [`DEEP`]'s anchors fire every corridor cell.
///
/// # Panics
///
/// If the cell is unreachable (it has no witness).
pub fn isolated_spec(cell: &Cell, configuration: &Configuration, seed: u64) -> CampaignSpec {
    assert!(cell.reachable(), "the cell {} has no witness", cell.label);
    let fixed = ancestor_holes(cell);
    let mut spec = spec_on(&DEEP, cell, configuration, seed);
    spec.proposers.anchors_first = false;
    for (hole, literal) in spec.holes.iter_mut().zip(DEEP.literals()) {
        if fixed.contains(hole.name.as_str()) {
            let value = cell
                .witness
                .iter()
                .find(|(name, _)| *name == hole.name)
                .map_or(0, |(_, value)| *value);
            assert_eq!(
                literal,
                value.to_string(),
                "{}'s anchor of {}",
                DEEP.file,
                hole.name
            );
            hole.constraints.choices = Some(vec![Value::Int(value.into())]);
        }
    }
    spec
}

/// The campaign that measures `cell` under `configuration` at `seed`, on [`WALK`].
pub fn spec(cell: &Cell, configuration: &Configuration, seed: u64) -> CampaignSpec {
    spec_on(&WALK, cell, configuration, seed)
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
                name: program.file.into(),
                text: program.text.into(),
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
        options: CaseOptions::default(),
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
    let mut campaign = Campaign::new(spec(cell, configuration, seed))
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
            "{} seed={} budget={} reached={}:",
            self.configuration,
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

/// The cells `budget` cases of `configuration` at `seed` fire, from one campaign aimed at `u3`,
/// which no case reaches, so that the campaign spends its whole budget and never shrinks.
///
/// This is the distinct-cells half of the metric, at the cost of one campaign. It is a
/// measurement of `configuration` only when its case sequence does not depend on the target
/// (the blind baseline): a target-directed configuration aimed at `u3` measures nothing about
/// the other cells. On the maze every walk ends cleanly with no undefined step, so a cell in
/// coverage `applied` fired on its leaf.
///
/// # Panics
///
/// As [`run_cell`].
pub fn run_coverage(configuration: &Configuration, seed: u64, budget: u64) -> CoverageRun {
    let (run, report) = run_cell(cell_named("u3"), configuration, seed, budget);
    assert_eq!(run.cases_to_hit, None, "u3 is unreachable");
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
        seed,
        budget,
        cells: CELLS
            .iter()
            .map(|cell| run_cell(cell, configuration, seed, budget).0)
            .collect(),
    }
}

/// Check what every configuration must satisfy on the maze: no unreachable cell is reached,
/// and a reached cell's parent is reached in no more cases, when the configuration's case
/// sequence does not depend on the target (`target_blind`; the blind baseline). A
/// target-directed configuration may reach a child before it reaches the parent on its own
/// campaign, so only the first property holds for it.
///
/// # Panics
///
/// On a violation.
pub fn check(run: &MazeRun, target_blind: bool) {
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

/// A table over several seeds of one configuration: per cell, the seeds that reached it and the
/// least, median and greatest cases to it over those seeds.
pub fn summary(runs: &[MazeRun]) -> String {
    let mut table = String::new();
    if let Some(first) = runs.first() {
        writeln!(
            table,
            "configuration {} budget {} seeds {:?}",
            first.configuration,
            first.budget,
            runs.iter().map(|run| run.seed).collect::<Vec<_>>()
        )
        .expect("writing to a String");
    }
    writeln!(table, "cell  guard        reached  min  median  max").expect("writing to a String");
    for (index, cell) in CELLS.iter().enumerate() {
        let mut cases: Vec<u64> = runs
            .iter()
            .filter_map(|run| run.cells[index].cases_to_hit)
            .collect();
        cases.sort_unstable();
        let stats = if cases.is_empty() {
            "-".to_owned()
        } else {
            format!(
                "{}  {}  {}",
                cases[0],
                cases[cases.len() / 2],
                cases[cases.len() - 1]
            )
        };
        let guard = format!("{:?}", cell.guard);
        writeln!(
            table,
            "{:<5} {guard:<12} {}/{}  {stats}",
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
