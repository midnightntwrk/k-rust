//! Tests of the dictionary proposer (ARCHITECTURE 8.3): the static harvest on the DICT and MAZE
//! fixtures, the per-hole pools under constraints and bounds, and the draws.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust::{backend::BackendError, k_rust_backend::definition::BackendDefinition};
use num_bigint::{BigInt, BigUint};
use rand::SeedableRng as _;
use rand_chacha::ChaCha20Rng;

use super::dictionary::{DRAW_PROBABILITY, DictionaryProposer, Harvest, HolePool, Literal, RADIUS};
use crate::{
    engine::proposer::{ProposalContext, Proposer as _},
    graph::RuleGraph,
    support::{self, Fixture},
    target::{RuleRef, resolve_rule},
    values::{
        Constraints, GenerationBounds, Generator, IntRange, LengthRange, Value, ValueSort,
        resolve_value_sort,
    },
};

/// The rule graph of `fixture` and the id of its rule labelled `label`.
fn graph_and_id(fixture: &'static Fixture, label: &str) -> (RuleGraph, String) {
    let mut backend = fixture.compiled().source_backend();
    let catalog = backend.rule_catalog(None).expect("a catalog");
    let id = resolve_rule(&catalog, &RuleRef::Label(label.into())).expect("a rule");
    let graph = RuleGraph::of_backend(&mut backend).expect("a graph");
    (graph, id)
}

fn int(value: i64) -> Literal {
    Literal::Domain {
        sort: "SortInt{}".into(),
        text: value.to_string().into_bytes(),
    }
}

fn string(text: &str) -> Literal {
    Literal::Domain {
        sort: "SortString{}".into(),
        text: text.as_bytes().to_vec(),
    }
}

/// The literals of `harvest` that are `Int`, `String` or constants of DICT's `Mode`, with their
/// distances: the ones these tests reason about.
fn relevant(harvest: &Harvest) -> BTreeMap<Literal, usize> {
    harvest
        .literals()
        .iter()
        .filter(|(literal, _)| match literal {
            Literal::Domain { sort, .. } => sort == "SortInt{}" || sort == "SortString{}",
            Literal::Constant { symbol } => {
                ["Lblfast", "Lblslow", "Lblidle"].contains(&symbol.as_str())
            }
        })
        .map(|(literal, distance)| (literal.clone(), *distance))
        .collect()
}

fn constant(harvest: &Harvest, name: &str) -> Option<usize> {
    harvest
        .literals()
        .iter()
        .find(|(literal, _)| {
            matches!(literal, Literal::Constant { symbol } if *symbol == format!("Lbl{name}"))
        })
        .map(|(_, distance)| *distance)
}

#[test]
fn the_harvest_reads_the_target_its_enablers_and_the_equations_its_guard_calls() {
    let (graph, goal) = graph_and_id(&support::DICT, "DICT.goal");
    let harvest = Harvest::from_graph(&graph, Some(&goal), RADIUS);
    let literals = relevant(&harvest);
    // `goal`'s guard `limit(N) ==Int 1` (distance 0), the conditions of `limit`'s equation
    // (`N >Int 500`) and of `cap`'s, which `limit-big` calls (`N ==Int 777`), at the distance
    // of the rule whose `requires` calls them; `gate`'s "open" one edge before.
    assert_eq!(literals.get(&int(1)), Some(&0), "{literals:?}");
    assert_eq!(literals.get(&int(500)), Some(&0), "{literals:?}");
    assert_eq!(literals.get(&int(777)), Some(&0), "{literals:?}");
    assert_eq!(literals.get(&string("open")), Some(&1), "{literals:?}");
    // `goal`'s left-hand side's constant constructor.
    assert_eq!(constant(&harvest, "fast"), Some(0), "{literals:?}");
    // `pre` is three edges before `goal`, `far` reaches it not at all, and the right-hand sides
    // of the equations (`0`, `2`) are no conditions.
    for absent in [int(4242), string("early"), int(123_456), int(2), int(0)] {
        assert!(
            !literals.contains_key(&absent),
            "{absent:?} in {literals:?}"
        );
    }
    assert_eq!(constant(&harvest, "idle"), None, "{literals:?}");
}

#[test]
fn the_radius_bounds_the_rules_harvested() {
    let (graph, goal) = graph_and_id(&support::DICT, "DICT.goal");
    let own = relevant(&Harvest::from_graph(&graph, Some(&goal), 0));
    assert!(own.contains_key(&int(777)), "{own:?}");
    assert!(!own.contains_key(&string("open")), "{own:?}");
    let wide = Harvest::from_graph(&graph, Some(&goal), 3);
    let literals = relevant(&wide);
    assert_eq!(literals.get(&int(4242)), Some(&3), "{literals:?}");
    assert!(!literals.contains_key(&int(123_456)), "{literals:?}");
    // `pre`'s right-hand side `run(N, "early", idle)` is no guard.
    assert!(!literals.contains_key(&string("early")), "{literals:?}");
    assert_eq!(constant(&wide, "idle"), None, "{literals:?}");
}

#[test]
fn an_owise_target_harvests_the_rules_it_competes_with() {
    let (graph, goal_else) = graph_and_id(&support::DICT, "DICT.goal-else");
    let harvest = Harvest::from_graph(&graph, Some(&goal_else), RADIUS);
    let literals = relevant(&harvest);
    // `goal-else` has no guard of its own: it applies where `goal` does not, so `goal`'s guard
    // and the equations it calls are its constants.
    for present in [int(1), int(500), int(777)] {
        assert_eq!(
            literals.get(&present),
            Some(&0),
            "{present:?} in {literals:?}"
        );
    }
    assert_eq!(constant(&harvest, "fast"), Some(0), "{literals:?}");
    // `goal` competes with no higher-priority rule, so its harvest holds nothing of
    // `goal-else`; and `gate-else` (beside `gate`) is no enabler of `goal`.
    let (graph, gate_else) = graph_and_id(&support::DICT, "DICT.gate-else");
    let literals = relevant(&Harvest::from_graph(&graph, Some(&gate_else), 0));
    assert_eq!(literals.get(&string("open")), Some(&0), "{literals:?}");
}

#[test]
fn a_target_without_a_rule_harvests_every_rule() {
    let (graph, _) = graph_and_id(&support::DICT, "DICT.goal");
    let literals = relevant(&Harvest::from_graph(&graph, None, RADIUS));
    for present in [int(123_456), int(4242), int(777), string("open")] {
        assert_eq!(
            literals.get(&present),
            Some(&0),
            "{present:?} in {literals:?}"
        );
    }
}

#[test]
fn the_maze_harvest_of_an_exact_cell_holds_its_constant_at_distance_zero() {
    let (graph, c5) = graph_and_id(&support::MAZE, "MAZE.c5");
    let literals = relevant(&Harvest::from_graph(&graph, Some(&c5), RADIUS));
    assert_eq!(literals.get(&int(31_337)), Some(&0), "{literals:?}");
    // `c4`'s bounds one edge before, and `c3`'s constant within the radius.
    assert_eq!(literals.get(&int(1000)), Some(&1), "{literals:?}");
    assert_eq!(literals.get(&int(1100)), Some(&1), "{literals:?}");
    assert!(
        literals.get(&int(7)).is_some_and(|distance| *distance <= 2),
        "{literals:?}"
    );
}

fn harvest_of(literals: &[(Literal, usize)]) -> Harvest {
    Harvest::from_literals(literals.iter().cloned().collect())
}

fn ints(values: &[i64]) -> BTreeSet<Value> {
    values
        .iter()
        .map(|value| Value::Int((*value).into()))
        .collect()
}

#[test]
fn an_int_pool_holds_the_constants_their_neighbours_and_negations_weighted_by_distance() {
    let harvest = harvest_of(&[(int(7), 0), (int(1000), 2), (string("x"), 0)]);
    let pool = HolePool::new(
        &harvest,
        &ValueSort::Int,
        &Constraints::default(),
        &GenerationBounds::default(),
    );
    assert_eq!(
        pool.values(),
        ints(&[
            4, 5, 6, 7, 8, 9, 10, -7, 997, 998, 999, 1000, 1001, 1002, 1003, -1000
        ])
    );
    assert_eq!(
        pool.exact(),
        BTreeMap::from([(Value::Int(7.into()), 16), (Value::Int(1000.into()), 1)])
    );
}

#[test]
fn a_pool_keeps_only_values_the_constraints_and_bounds_admit() {
    let harvest = harvest_of(&[(int(777), 0), (int(500), 0), (int(1), 0)]);
    let range = Constraints {
        range: Some(IntRange {
            min: Some(BigInt::from(0)),
            max: Some(BigInt::from(600)),
        }),
        ..Constraints::default()
    };
    let pool = HolePool::new(
        &harvest,
        &ValueSort::Int,
        &range,
        &GenerationBounds::default(),
    );
    assert_eq!(
        pool.values(),
        ints(&[0, 2, 3, 4, 497, 498, 499, 500, 501, 502, 503, 1])
    );
    let choices = Constraints {
        choices: Some(vec![Value::Int(1.into()), Value::Int(9.into())]),
        ..Constraints::default()
    };
    let pool = HolePool::new(
        &harvest,
        &ValueSort::Int,
        &choices,
        &GenerationBounds::default(),
    );
    assert_eq!(pool.values(), ints(&[1]));
    // Four bits of magnitude: |v| < 16.
    let small = GenerationBounds {
        int_bits: 4,
        ..GenerationBounds::default()
    };
    let pool = HolePool::new(&harvest, &ValueSort::Int, &Constraints::default(), &small);
    assert_eq!(pool.values(), ints(&[-2, -1, 0, 1, 2, 3, 4]));
    // One bounded end: within `int_bits` bits of the admissible value nearest zero (1000).
    let above = Constraints {
        range: Some(IntRange {
            min: Some(BigInt::from(1000)),
            max: None,
        }),
        ..Constraints::default()
    };
    let near = HolePool::new(
        &harvest_of(&[(int(1003), 0), (int(1020), 0)]),
        &ValueSort::Int,
        &above,
        &small,
    );
    assert_eq!(
        near.values(),
        ints(&[1000, 1001, 1002, 1003, 1004, 1005, 1006])
    );
}

#[test]
fn string_pools_respect_the_length_bounds_and_other_sorts_take_nothing() {
    let harvest = harvest_of(&[(string("open"), 1), (string("ab"), 0), (int(3), 0)]);
    let pool = HolePool::new(
        &harvest,
        &ValueSort::String,
        &Constraints::default(),
        &GenerationBounds::default(),
    );
    assert_eq!(
        pool.values(),
        BTreeSet::from([Value::String("ab".into()), Value::String("open".into())])
    );
    let short = Constraints {
        length: Some(LengthRange {
            min: None,
            max: Some(3),
        }),
        ..Constraints::default()
    };
    let pool = HolePool::new(
        &harvest,
        &ValueSort::String,
        &short,
        &GenerationBounds::default(),
    );
    assert_eq!(pool.values(), BTreeSet::from([Value::String("ab".into())]));
    let pool = HolePool::new(
        &harvest,
        &ValueSort::Bytes,
        &Constraints::default(),
        &GenerationBounds::default(),
    );
    assert!(pool.is_empty());
}

#[test]
fn an_mint_pool_stays_inside_its_width() {
    let harvest = harvest_of(&[(
        Literal::Domain {
            sort: "SortMInt{Sort8{}}".into(),
            text: b"255p8".to_vec(),
        },
        0,
    )]);
    let pool = HolePool::new(
        &harvest,
        &ValueSort::MInt { width: 8 },
        &Constraints::default(),
        &GenerationBounds::default(),
    );
    let mint = |value: u32| Value::MInt {
        width: 8,
        value: BigUint::from(value),
    };
    assert_eq!(
        pool.values(),
        [252, 253, 254, 255, 1].into_iter().map(mint).collect()
    );
    // Another width's literal is no value of this hole.
    let pool = HolePool::new(
        &harvest,
        &ValueSort::MInt { width: 16 },
        &Constraints::default(),
        &GenerationBounds::default(),
    );
    assert!(pool.is_empty());
}

#[test]
fn a_data_pool_takes_the_constant_constructors_of_its_sort() {
    let (graph, goal) = graph_and_id(&support::DICT, "DICT.goal");
    let harvest = Harvest::from_graph(&graph, Some(&goal), RADIUS);
    let mut backend = support::DICT.compiled().source_backend();
    let mode = backend
        .with_solver_over(None, &[], |definition: &BackendDefinition, _| {
            Ok::<_, BackendError>(
                resolve_value_sort("Mode", &Constraints::default(), definition).expect("Mode"),
            )
        })
        .expect("a definition");
    let pool = HolePool::new(
        &harvest,
        &mode,
        &Constraints::default(),
        &GenerationBounds::default(),
    );
    let symbols: BTreeSet<String> = pool
        .values()
        .into_iter()
        .map(|value| match value {
            Value::Apply { symbol, arguments } if arguments.is_empty() => symbol,
            other => panic!("not a constant: {other:?}"),
        })
        .collect();
    // `fast` (`goal`'s left-hand side); `idle` is only in `pre`'s right-hand side and `slow`
    // in no rule.
    assert_eq!(symbols, BTreeSet::from(["Lblfast".to_owned()]));
}

fn proposals(seed: u64, count: usize) -> Vec<Value> {
    let harvest = harvest_of(&[(int(31_337), 0)]);
    let bounds = GenerationBounds::default();
    let pool = HolePool::new(&harvest, &ValueSort::Int, &Constraints::default(), &bounds);
    let generators =
        vec![Generator::new(&ValueSort::Int, &Constraints::default(), &bounds).unwrap()];
    let mut proposer = DictionaryProposer::new(Arc::new(vec![pool]), generators, seed);
    let mut schedule = ChaCha20Rng::seed_from_u64(0);
    (0..count)
        .map(|_| {
            let mut context = ProposalContext { rng: &mut schedule };
            let mut proposal = proposer.propose(&mut context).expect("never exhausted");
            assert!(proposal.failure.is_none());
            proposal.values.pop().expect("one hole")
        })
        .collect()
}

#[test]
fn the_dictionary_draws_from_the_pool_with_its_fixed_probability_and_deterministically() {
    let first = proposals(7, 2000);
    assert_eq!(
        first,
        proposals(7, 2000),
        "the same seed draws the same values"
    );
    assert_ne!(first, proposals(8, 2000), "another seed draws other values");
    let harvested = ints(&[
        31_334, 31_335, 31_336, 31_337, 31_338, 31_339, 31_340, -31_337,
    ]);
    let from_pool = first
        .iter()
        .filter(|value| harvested.contains(value))
        .count();
    let exact = first
        .iter()
        .filter(|value| **value == Value::Int(31_337.into()))
        .count();
    // DRAW_PROBABILITY is 1/2: about 1000 pool draws, about half of them the constant itself.
    assert_eq!(DRAW_PROBABILITY, (1, 2));
    assert!((900..1100).contains(&from_pool), "{from_pool}");
    assert!((400..600).contains(&exact), "{exact}");
}

#[test]
fn conditions_written_in_equation_right_hand_sides_are_harvested() {
    // `good(N) => N ==Int 4711`: a Boolean helper's condition is its right-hand side.
    let (graph, pgoal) = graph_and_id(&support::DICT, "DICT.pgoal");
    let literals = relevant(&Harvest::from_graph(&graph, Some(&pgoal), RADIUS));
    assert_eq!(literals.get(&int(4711)), Some(&0), "{literals:?}");
    // `pick(N) => #if N ==Int 31337 #then 1 #else 0 #fi`: the condition of the `#if`, not its
    // branches, which are values.
    let (graph, igoal) = graph_and_id(&support::DICT, "DICT.igoal");
    let literals = relevant(&Harvest::from_graph(&graph, Some(&igoal), RADIUS));
    assert_eq!(literals.get(&int(31_337)), Some(&0), "{literals:?}");
    assert!(!literals.contains_key(&int(0)), "{literals:?}");
}

#[test]
fn a_differential_harvest_puts_the_rules_that_differ_first() {
    let graph = |fixture: &'static Fixture| {
        RuleGraph::of_backend(&mut fixture.compiled().source_backend()).expect("a graph")
    };
    let harvest = Harvest::differential(&graph(&support::COIN), &graph(&support::COIN_KILL));
    let literals = relevant(&harvest);
    // COIN-KILL's `heads`, `tails` (`N <=Int 10`) and `skew` (`N >Int 10`) are not COIN's rules;
    // `count-step` and `count-done` are the same rules on both sides.
    assert_eq!(literals.get(&int(10)), Some(&0), "{literals:?}");
    assert_eq!(literals.get(&int(0)), Some(&1), "{literals:?}");
}
