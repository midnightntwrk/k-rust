//! The list-shaped stall benchmark's harness (FZ-14; ARCHITECTURE 8.5, 11): the lock of
//! `lock.k`, its cells, and the metric of the maze (`maze/harness.rs`): per proposer
//! configuration and seed, the cases to each cell, every cell measured by its own campaign
//! whose target is the cell's rule in mode `fired`, without shrinking.
//!
//! A test binary includes this file with `#[path = "data/lock/harness.rs"] mod lock;`, beside
//! `mod support;` and the maze's harness as `mod maze;` (for [`Configuration`]) at its root.

#![allow(dead_code, reason = "each test binary uses a subset of the harness")]

use std::{collections::BTreeMap, fmt::Write as _, sync::Arc};

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, OutcomeClass, ProgramInput, Target, TargetKind, Value,
    report::{CampaignOutcome, FuzzReport, HitLabel},
    spec::DEFAULT_REJECTION_CAP,
    target::{RuleMode, RuleRef, RuleTarget},
    values::{Constraints, ElementSorts, GenerationBounds},
};

use super::maze::Configuration;

/// One cell of the lock: a rule target.
#[derive(Clone, Copy, Debug)]
pub struct Cell {
    /// The rule's label in `lock.k` (module `LOCK`).
    pub label: &'static str,
    /// The keys of a list that fires the cell, each the passing value nearest 0; empty for
    /// the unreachable cell.
    pub witness: &'static [i64],
}

impl Cell {
    /// Some list fires the cell.
    pub fn reachable(&self) -> bool {
        !self.witness.is_empty()
    }
}

/// Every cell: the corridor `l1` .. `l5`, then the negative control `lu`.
pub const CELLS: [Cell; 6] = [
    Cell {
        label: "l1",
        witness: &[17],
    },
    Cell {
        label: "l2",
        witness: &[17, 1001],
    },
    Cell {
        label: "l3",
        witness: &[17, 1001, 31337],
    },
    Cell {
        label: "l4",
        witness: &[17, 1001, 31337, -5001],
    },
    Cell {
        label: "l5",
        witness: &[17, 1001, 31337, -5001, 4242],
    },
    Cell {
        label: "lu",
        witness: &[],
    },
];

/// The cell labelled `label`.
///
/// # Panics
///
/// If no cell has that label.
pub fn cell_named(label: &str) -> &'static Cell {
    CELLS
        .iter()
        .find(|cell| cell.label == label)
        .unwrap_or_else(|| panic!("no lock cell {label}"))
}

/// A list of `Int`s as a value.
pub fn keys(keys: &[i64]) -> Value {
    Value::List(keys.iter().map(|key| Value::Int((*key).into())).collect())
}

/// The campaign that measures `cell` under `configuration` at `seed`: the program `open`, the
/// hole `KEYS` on the configuration variable `$KEYS` (a `List` of `Int`, anchor `ListItem(0)`),
/// the cell's rule fired as the target, no shrinking.
pub fn spec(cell: &Cell, configuration: &Configuration, seed: u64) -> CampaignSpec {
    list_spec(
        &super::support::LOCK,
        "lock/open.pgm",
        "KEYS",
        "Int",
        &format!("LOCK.{}", cell.label),
        configuration,
        seed,
    )
}

/// The campaign on `fixture`'s program `program` whose one hole is the configuration variable
/// `variable`, a `List` of `element`, with the rule `rule` fired as the target and no
/// shrinking: the lock's, and the bank's (`bank/harness.rs`).
pub fn list_spec(
    fixture: &'static super::support::Fixture,
    program: &str,
    variable: &str,
    element: &str,
    rule: &str,
    configuration: &Configuration,
    seed: u64,
) -> CampaignSpec {
    let compiled = fixture.compiled();
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        },
        program: ProgramInput::Source(compiled.program_source(program)),
        holes: vec![HoleDecl {
            name: variable.into(),
            sort: "List".into(),
            location: HoleLocation::ConfigVar {
                name: variable.into(),
            },
            constraints: Constraints {
                elements: Some(ElementSorts::Elements {
                    element: element.into(),
                }),
                ..Constraints::default()
            },
            allow_refused_sort: false,
        }],
        target: Target {
            kind: TargetKind::Rule(RuleTarget {
                rule: RuleRef::Label(rule.into()),
                mode: RuleMode::Fired,
            }),
            run_to_completion: false,
            negated_property: false,
        },
        options: CaseOptions {
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

/// Run the campaign that measures `cell`: the cases to its first confirmed hit (`None` when
/// none within `budget`), with the report.
///
/// # Panics
///
/// If the campaign is refused, reports an engine defect, or has a case other than a clean
/// `miss` or the one `hit` that ended it: every list ends naturally, so any other class is a
/// defect of the benchmark or of the engine.
pub fn run_cell(
    cell: &Cell,
    configuration: &Configuration,
    seed: u64,
    budget: u64,
) -> (Option<u64>, FuzzReport) {
    run_spec(cell.label, spec(cell, configuration, seed), budget)
}

/// [`run_cell`] on any campaign whose target cell is labelled `label`.
///
/// # Panics
///
/// As [`run_cell`].
pub fn run_spec(label: &str, spec: CampaignSpec, budget: u64) -> (Option<u64>, FuzzReport) {
    let mut campaign = Campaign::new(spec)
        .unwrap_or_else(|error| panic!("cell {label}: the campaign is refused: {error}"));
    let report = campaign.run(Budget::Cases(budget), None);
    assert!(
        report.engine_defects.is_empty(),
        "cell {label}: {:#?}",
        report.engine_defects
    );
    let cases_to_hit = match &report.outcome {
        CampaignOutcome::WitnessFound { witness } => {
            assert_eq!(witness.label, HitLabel::Hit, "cell {label}");
            Some(report.totals.cases)
        }
        CampaignOutcome::NoWitnessFound { .. } => None,
        other => panic!("cell {label}: the campaign ended {other:?}"),
    };
    let hits = u64::from(cases_to_hit.is_some());
    let mut expected = BTreeMap::from([(OutcomeClass::Miss, report.totals.cases - hits)]);
    if hits == 1 {
        expected.insert(OutcomeClass::Hit, 1);
    }
    expected.retain(|_, count| *count > 0);
    assert_eq!(
        report.totals.classes, expected,
        "cell {label}: every case is a clean miss or the hit"
    );
    assert_eq!(report.totals.outside_determinism, 0, "cell {label}");
    (cases_to_hit, report)
}

/// The cases to each of `labels` under `configuration` at `seed`, as one line:
/// `blind seed=1 budget=5000: l1=2043 l2=- ...` (`-`: not reached).
///
/// # Panics
///
/// As [`run_cell`], and if an unreachable cell is reached.
pub fn run_line(
    configuration: &Configuration,
    labels: &[&str],
    seed: u64,
    budget: u64,
) -> (String, Vec<Option<u64>>) {
    let mut line = format!("{} seed={seed} budget={budget}:", configuration.name);
    let mut cases = Vec::new();
    for label in labels {
        let cell = cell_named(label);
        let (hit, _) = run_cell(cell, configuration, seed, budget);
        assert!(
            cell.reachable() || hit.is_none(),
            "{line}: the unreachable cell {label} was reached"
        );
        match hit {
            Some(hit) => write!(line, " {label}={hit}"),
            None => write!(line, " {label}=-"),
        }
        .expect("writing to a String");
        cases.push(hit);
    }
    (line, cases)
}

/// An unreached seed counts as more than the budget and sorts after every number.
fn censored(cases: Option<u64>) -> (bool, u64) {
    cases.map_or((true, 0), |cases| (false, cases))
}

/// The censored lower median of one cell's cases over several seeds (`maze::censored_median`):
/// `None` when it is unreached.
pub fn censored_median(cases: &[Option<u64>]) -> Option<u64> {
    let mut sorted: Vec<(bool, u64)> = cases.iter().copied().map(censored).collect();
    sorted.sort_unstable();
    let (unreached, median) = sorted[(sorted.len() - 1) / 2];
    (!unreached).then_some(median)
}

/// Per-seed (wins, losses, ties) of `candidate` against `baseline` at the same seeds
/// (`maze::pairwise`).
pub fn pairwise(candidate: &[Option<u64>], baseline: &[Option<u64>]) -> (u64, u64, u64) {
    assert_eq!(candidate.len(), baseline.len(), "the same seeds");
    let mut tally = (0, 0, 0);
    for (ours, theirs) in candidate.iter().zip(baseline) {
        match censored(*ours).cmp(&censored(*theirs)) {
            std::cmp::Ordering::Less => tally.0 += 1,
            std::cmp::Ordering::Greater => tally.1 += 1,
            std::cmp::Ordering::Equal => tally.2 += 1,
        }
    }
    tally
}

/// `reached/seeds, censored median` of one cell over several seeds: `7/10, 412`.
pub fn summary(cases: &[Option<u64>], budget: u64) -> String {
    let reached = cases.iter().filter(|cases| cases.is_some()).count();
    let median =
        censored_median(cases).map_or_else(|| format!(">{budget}"), |median| median.to_string());
    format!("{reached}/{}, {median}", cases.len())
}
