//! The loop-shaped stall benchmark's harness (FZ-17): the tally of `tally.k`, its depth cells,
//! and the lock's metric (`lock/harness.rs`, whose campaign builder and runner it uses).
//!
//! A test binary includes this file with `#[path = "data/tally/harness.rs"] mod tally;`, beside
//! the lock's harness as `mod lock;`, the maze's as `mod maze;` and `mod support;`.

#![allow(dead_code, reason = "each test binary uses a subset of the harness")]

use std::fmt::Write as _;

use k_rust_fuzz::{
    CampaignSpec, TargetKind, Value,
    target::{PatternAt, PatternTarget},
};

use super::maze::Configuration;

/// The depth cells: a list of which at least `d` keys applied, for each `d` here.
pub const DEPTHS: [u64; 3] = [4, 8, 16];

/// A definition of the tally: the clean one (`tally.k`), or one with work at the end of the
/// walk proportional to the keys left after the loop, by an equation (`noise.k`) or by a
/// rewrite rule (`drain.k`). All three have the same `eat`, program, hole and cells.
#[derive(Clone, Copy, Debug)]
pub enum Variant {
    Clean,
    Noise,
    Drain,
}

impl Variant {
    pub fn name(self) -> &'static str {
        match self {
            Self::Clean => "tally",
            Self::Noise => "noise",
            Self::Drain => "drain",
        }
    }

    fn fixture(self) -> &'static super::support::Fixture {
        match self {
            Self::Clean => &super::support::TALLY,
            Self::Noise => &super::support::NOISE,
            Self::Drain => &super::support::DRAIN,
        }
    }

    fn eat(self) -> &'static str {
        match self {
            Self::Clean => "TALLY.eat",
            Self::Noise => "NOISE.eat",
            Self::Drain => "DRAIN.eat",
        }
    }
}

/// A list of keys as a value.
pub fn keys(keys: &[i64]) -> Value {
    Value::List(keys.iter().map(|key| Value::Int((*key).into())).collect())
}

/// The campaign that measures depth `depth`: the program `count`, the hole `KEYS` (a `List` of
/// `Int`, anchor `ListItem(0)`, which `eat` refuses), the pattern
/// `<k> .K </k> <n> N </n> requires N >=Int depth` on the final configuration, no shrinking.
/// The climb refuses pattern targets, so only configurations without it measure these cells.
pub fn depth_spec(depth: u64, configuration: &Configuration, seed: u64) -> CampaignSpec {
    variant_spec(Variant::Clean, depth, configuration, seed)
}

/// [`depth_spec`] on `variant`.
pub fn variant_spec(
    variant: Variant,
    depth: u64,
    configuration: &Configuration,
    seed: u64,
) -> CampaignSpec {
    let mut spec = super::lock::list_spec(
        variant.fixture(),
        "tally/run.pgm",
        "KEYS",
        "Int",
        variant.eat(),
        configuration,
        seed,
    );
    spec.target.kind = TargetKind::Pattern(PatternTarget {
        pattern: format!("<k> .K </k> <n> N:Int </n> requires N >=Int {depth}"),
        at: PatternAt::Final,
    });
    spec
}

/// The cases to each depth of [`DEPTHS`] as one line, in `lock::run_line`'s format with the
/// cells named `d4`, `d8`, `d16`.
///
/// # Panics
///
/// As `lock::run_spec`.
pub fn depth_line(
    configuration: &Configuration,
    seed: u64,
    budget: u64,
) -> (String, Vec<Option<u64>>) {
    variant_line(Variant::Clean, configuration, seed, budget)
}

/// [`depth_line`] on `variant`.
///
/// # Panics
///
/// As `lock::run_spec`.
pub fn variant_line(
    variant: Variant,
    configuration: &Configuration,
    seed: u64,
    budget: u64,
) -> (String, Vec<Option<u64>>) {
    let mut line = format!("{} seed={seed} budget={budget}:", configuration.name);
    let mut cases = Vec::new();
    for depth in DEPTHS {
        let label = format!("d{depth}");
        let (hit, _) = super::lock::run_spec(
            &label,
            variant_spec(variant, depth, configuration, seed),
            budget,
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
