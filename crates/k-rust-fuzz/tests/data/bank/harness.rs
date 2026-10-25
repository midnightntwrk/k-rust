//! The ledger-shaped stall benchmark's harness (FZ-14 round 2): the bank of `bank.k`, its cells,
//! and the lock's metric (`lock/harness.rs`, whose campaign builder and runner it uses).
//!
//! A test binary includes this file with `#[path = "data/bank/harness.rs"] mod bank;`, beside
//! the lock's harness as `mod lock;`, the maze's as `mod maze;` and `mod support;`.

#![allow(dead_code, reason = "each test binary uses a subset of the harness")]

use std::fmt::Write as _;

use k_rust_fuzz::{
    CampaignSpec, TargetKind, Value,
    report::FuzzReport,
    target::{PatternAt, PatternTarget},
};

use super::maze::Configuration;

/// One cell of the bank: a rule target, and a list of `(nonce, amount)` transactions that fires
/// it (empty for the unreachable cell).
#[derive(Clone, Copy, Debug)]
pub struct Cell {
    pub label: &'static str,
    pub witness: &'static [(i64, i64)],
}

impl Cell {
    pub fn reachable(&self) -> bool {
        !self.witness.is_empty()
    }
}

/// Every cell: one valid transaction (`pay`), an exact doubling from the third transaction on
/// (`double`), five transactions reaching 2000 (`rich`), and the negative control `broke`.
pub const CELLS: [Cell; 4] = [
    Cell {
        label: "pay",
        witness: &[(0, 1)],
    },
    Cell {
        label: "double",
        witness: &[(0, 100), (1, 200), (2, 400)],
    },
    Cell {
        label: "rich",
        witness: &[(0, 100), (1, 200), (2, 400), (3, 800), (4, 1600)],
    },
    Cell {
        label: "broke",
        witness: &[],
    },
];

pub fn cell_named(label: &str) -> &'static Cell {
    CELLS
        .iter()
        .find(|cell| cell.label == label)
        .unwrap_or_else(|| panic!("no bank cell {label}"))
}

/// A list of transactions as a value.
pub fn txs(txs: &[(i64, i64)]) -> Value {
    Value::List(
        txs.iter()
            .map(|(nonce, amount)| Value::Apply {
                symbol: "Lbltx".into(),
                arguments: vec![Value::Int((*nonce).into()), Value::Int((*amount).into())],
            })
            .collect(),
    )
}

/// The campaign that measures `cell`: the program `run`, the hole `TXS` (a `List` of `Tx`,
/// anchor `ListItem(tx(7, 1))`, whose nonce is wrong), the cell's rule fired, no shrinking.
pub fn spec(cell: &Cell, configuration: &Configuration, seed: u64) -> CampaignSpec {
    super::lock::list_spec(
        &super::support::BANK,
        "bank/run.pgm",
        "TXS",
        "Tx",
        &format!("BANK.{}", cell.label),
        configuration,
        seed,
    )
}

/// The cases to `cell`'s first confirmed hit, with the report (`lock::run_spec`).
pub fn run_cell(
    cell: &Cell,
    configuration: &Configuration,
    seed: u64,
    budget: u64,
) -> (Option<u64>, FuzzReport) {
    super::lock::run_spec(cell.label, spec(cell, configuration, seed), budget)
}

/// The cases to each of `labels` as one line (`lock::run_line`'s format).
///
/// # Panics
///
/// As `lock::run_spec`, and if the unreachable cell is reached.
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

/// The loop-depth cells (FZ-17): a list of which at least `depth` transactions applied, the
/// final configuration's nonce being the number applied. They measure the progress one more
/// applied transaction makes, apart from the exact, state-relative amounts `double` and `rich`
/// also need; `pay` is depth 1.
pub const DEPTHS: [u64; 4] = [3, 5, 8, 12];

/// The campaign that measures depth `depth`: [`spec`]'s, with the target the pattern
/// `<k> .K </k> <nonce> M </nonce> requires M >=Int depth` on the final configuration. The
/// climb refuses pattern targets, so only configurations without it measure these cells.
pub fn depth_spec(depth: u64, configuration: &Configuration, seed: u64) -> CampaignSpec {
    let mut spec = spec(cell_named("pay"), configuration, seed);
    spec.target.kind = TargetKind::Pattern(PatternTarget {
        pattern: format!("<k> .K </k> <nonce> M:Int </nonce> requires M >=Int {depth}"),
        at: PatternAt::Final,
    });
    spec
}

/// The cases to each depth of [`DEPTHS`] as one line, in `run_line`'s format with the cells
/// named `d3`, `d5`, ...
///
/// # Panics
///
/// As `lock::run_spec`.
pub fn depth_line(
    configuration: &Configuration,
    seed: u64,
    budget: u64,
) -> (String, Vec<Option<u64>>) {
    let mut line = format!("{} seed={seed} budget={budget}:", configuration.name);
    let mut cases = Vec::new();
    for depth in DEPTHS {
        let label = format!("d{depth}");
        let (hit, _) =
            super::lock::run_spec(&label, depth_spec(depth, configuration, seed), budget);
        match hit {
            Some(hit) => write!(line, " {label}={hit}"),
            None => write!(line, " {label}=-"),
        }
        .expect("writing to a String");
        cases.push(hit);
    }
    (line, cases)
}
