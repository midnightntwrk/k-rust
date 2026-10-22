//! Unit tests of the climb proposer's moves, admissibility and acceptance, without a
//! definition: scores are given, not computed.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use rand_chacha::ChaCha20Rng;

use super::*;
use crate::{
    engine::proposer::{Observation, Origin, Proposal, ProposalContext, Proposer},
    exec::OutcomeClass,
    score::{Distance, Guard, Level, Score},
    values::{IntRange, LengthRange},
};

fn bounds() -> GenerationBounds {
    GenerationBounds {
        int_bits: 64,
        length: 8,
        depth: 4,
    }
}

fn hole(sort: ValueSort, constraints: Constraints) -> ClimbHole {
    let generator = Generator::new(&sort, &constraints, &bounds()).expect("a generator");
    ClimbHole {
        sort,
        constraints,
        generator,
    }
}

fn int(value: i64) -> Value {
    Value::Int(BigInt::from(value))
}

fn score(raw: u32) -> Score {
    Score {
        level: Level::At(0),
        guard: Guard::Defined(Distance::normalized(raw.into())),
    }
}

fn observation(score: Option<Score>) -> Observation {
    Observation {
        case: 0,
        class: if score.is_some() {
            OutcomeClass::Miss
        } else {
            OutcomeClass::Stuck
        },
        applied: Vec::new(),
        matched: Vec::new(),
        work: 1,
        score,
        reads: Vec::new(),
        blocked: None,
        comparisons: Vec::new(),
    }
}

fn propose(climb: &mut ClimbProposer) -> Proposal {
    let mut rng = ChaCha20Rng::from_seed([7; 32]);
    climb
        .propose(&mut ProposalContext { rng: &mut rng })
        .expect("a climb proposal")
}

/// The integer a one-hole climb at `start` reaches after `steps` proposals, where a value's
/// score is its distance to `goal`.
fn climb_to(goal: i64, start: i64, steps: usize, seed: u64) -> (i64, usize) {
    let mut climb = ClimbProposer::new(
        vec![hole(ValueSort::Int, Constraints::default())],
        bounds(),
        seed,
    );
    let distance = |value: &Value| match value {
        Value::Int(number) => {
            u32::try_from((number - BigInt::from(goal)).magnitude().clone()).unwrap_or(u32::MAX)
        }
        _ => u32::MAX,
    };
    let anchors = Proposal::plain(Origin::Explicit, vec![int(start)]);
    climb.observe_all(
        &anchors,
        &observation(Some(score(distance(&anchors.values[0])))),
    );
    for step in 0..steps {
        let proposal = propose(&mut climb);
        let raw = distance(&proposal.values[0]);
        climb.observe(&proposal, &observation(Some(score(raw))), false);
        if raw == 0 {
            return (goal, step + 1);
        }
    }
    let best = climb.incumbent().expect("an incumbent").values[0].clone();
    match best {
        Value::Int(number) => (i64::try_from(number).expect("small"), steps),
        _ => unreachable!(),
    }
}

#[test]
fn the_climb_waits_for_a_scored_case() {
    let mut climb = ClimbProposer::new(
        vec![hole(ValueSort::Int, Constraints::default())],
        bounds(),
        1,
    );
    assert!(!climb.ready());
    // An unscored case (not a miss) gives nothing to climb from.
    let stuck = Proposal::plain(Origin::Explicit, vec![int(3)]);
    climb.observe_all(&stuck, &observation(None));
    assert!(!climb.ready());
    climb.observe_all(&stuck, &observation(Some(score(4))));
    assert!(climb.ready());
    assert_eq!(climb.budget_share(), Some((1, 2)));
}

#[test]
fn exponential_steps_reach_a_distant_integer_goal() {
    // From -3 to 1001: a climb with unit steps would need a thousand cases.
    for seed in 0..4 {
        let (reached, steps) = climb_to(1001, -3, 300, seed);
        assert_eq!(reached, 1001, "seed {seed}");
        assert!(steps < 300, "seed {seed}: {steps}");
    }
}

#[test]
fn foreign_cases_replace_the_incumbent_only_when_strictly_better_own_when_not_worse() {
    let mut climb = ClimbProposer::new(
        vec![hole(ValueSort::Int, Constraints::default())],
        bounds(),
        3,
    );
    let first = Proposal::plain(Origin::Explicit, vec![int(10)]);
    climb.observe_all(&first, &observation(Some(score(5))));
    let tie = Proposal::plain(Origin::Scheduled(ProposerKind::Blind), vec![int(20)]);
    climb.observe_all(&tie, &observation(Some(score(5))));
    assert_eq!(climb.incumbent().expect("best").values, vec![int(10)]);
    let better = Proposal::plain(Origin::Scheduled(ProposerKind::Blind), vec![int(30)]);
    climb.observe_all(&better, &observation(Some(score(4))));
    assert_eq!(climb.incumbent().expect("best").values, vec![int(30)]);
    // A climb case of equal score replaces it (ACCEPT_EQUAL); a worse or unscored one does not.
    let own = Proposal::plain(Origin::Scheduled(ProposerKind::Climb), vec![int(31)]);
    climb.observe(&own, &observation(Some(score(4))), false);
    climb.observe_all(&own, &observation(Some(score(4))));
    assert_eq!(climb.incumbent().expect("best").values, vec![int(31)]);
    let worse = Proposal::plain(Origin::Scheduled(ProposerKind::Climb), vec![int(40)]);
    climb.observe(&worse, &observation(Some(score(9))), false);
    assert_eq!(climb.incumbent().expect("best").values, vec![int(31)]);
    let unscored = Proposal::plain(Origin::Scheduled(ProposerKind::Climb), vec![int(41)]);
    climb.observe(&unscored, &observation(None), false);
    assert_eq!(climb.incumbent().expect("best").values, vec![int(31)]);
    // A move that leaves the guard without a distance (an undefined guard at the target: the
    // score's guard `Unknown`) scores worse than any defined miss at the same level, so it is
    // never accepted, from the climb or another proposer.
    let undefined = Score {
        level: Level::At(0),
        guard: Guard::Unknown,
    };
    let own = Proposal::plain(Origin::Scheduled(ProposerKind::Climb), vec![int(0)]);
    climb.observe(&own, &observation(Some(undefined.clone())), false);
    let foreign = Proposal::plain(Origin::Scheduled(ProposerKind::Blind), vec![int(0)]);
    climb.observe_all(&foreign, &observation(Some(undefined)));
    assert_eq!(climb.incumbent().expect("best").values, vec![int(31)]);
}

#[test]
fn every_move_is_admissible_and_changes_the_value() {
    let ranged = Constraints {
        range: Some(IntRange {
            min: Some(BigInt::from(-5)),
            max: Some(BigInt::from(5)),
        }),
        ..Constraints::default()
    };
    let bounded_length = Constraints {
        length: Some(LengthRange {
            min: Some(1),
            max: Some(3),
        }),
        ..Constraints::default()
    };
    let choices = Constraints {
        choices: Some(vec![int(1), int(2), int(3)]),
        ..Constraints::default()
    };
    let holes = vec![
        (hole(ValueSort::Int, ranged.clone()), int(0), ranged),
        (
            hole(ValueSort::Bool, Constraints::default()),
            Value::Bool(false),
            Constraints::default(),
        ),
        (
            hole(ValueSort::String, bounded_length.clone()),
            Value::String("ab".into()),
            bounded_length.clone(),
        ),
        (
            hole(ValueSort::Bytes, bounded_length.clone()),
            Value::Bytes(vec![1]),
            bounded_length,
        ),
        (hole(ValueSort::Int, choices.clone()), int(2), choices),
        (
            hole(ValueSort::MInt { width: 8 }, Constraints::default()),
            Value::MInt {
                width: 8,
                value: 255u32.into(),
            },
            Constraints::default(),
        ),
    ];
    let starts: Vec<Value> = holes.iter().map(|(_, start, _)| start.clone()).collect();
    let checks: Vec<(ValueSort, Constraints)> = holes
        .iter()
        .map(|(hole, _, constraints)| (hole.sort.clone(), constraints.clone()))
        .collect();
    let mut climb = ClimbProposer::new(
        holes.into_iter().map(|(hole, _, _)| hole).collect(),
        bounds(),
        5,
    );
    climb.observe_all(
        &Proposal::plain(Origin::Explicit, starts.clone()),
        &observation(Some(score(1))),
    );
    let mut moved = vec![false; starts.len()];
    for _ in 0..400 {
        let proposal = propose(&mut climb);
        assert_eq!(proposal.origin, Origin::Scheduled(ProposerKind::Climb));
        for (index, value) in proposal.values.iter().enumerate() {
            let (sort, constraints) = &checks[index];
            assert!(
                values::admissible(value, sort, constraints, &bounds()),
                "hole {index}: {value:?}"
            );
            moved[index] |= *value != starts[index];
        }
        let changed = proposal
            .values
            .iter()
            .zip(&starts)
            .filter(|(value, start)| value != start)
            .count();
        assert!((1..=2).contains(&changed), "{:?}", proposal.values);
        // Reject every move, so that each proposal moves from the starting values.
        climb.observe(&proposal, &observation(Some(score(2))), false);
    }
    assert!(moved.iter().all(|moved| *moved), "{moved:?}");
}

#[test]
fn collection_moves_keep_sets_and_maps_sorted_and_distinct() {
    use crate::values::{CollectionSymbols, ValueSort as S};
    let symbols = CollectionSymbols {
        kore_sort: "SortSet".into(),
        unit: "unit".into(),
        element: "element".into(),
        concat: "concat".into(),
        element_arguments: Vec::new(),
    };
    let set = S::Set {
        sort: "Set".into(),
        symbols: symbols.clone(),
        element: Box::new(S::Int),
        text: None,
    };
    let map = S::Map {
        sort: "Map".into(),
        symbols: symbols.clone(),
        key: Box::new(S::Int),
        value: Box::new(S::Bool),
        text: None,
    };
    let list = S::List {
        sort: "List".into(),
        symbols,
        element: Box::new(S::Int),
        text: None,
    };
    let starts = vec![
        Value::Set(vec![int(1), int(5)]),
        Value::Map(vec![
            (int(1), Value::Bool(true)),
            (int(4), Value::Bool(false)),
        ]),
        Value::List(vec![int(3)]),
    ];
    let sorts = [set, map, list];
    let mut climb = ClimbProposer::new(
        sorts
            .iter()
            .map(|sort| hole(sort.clone(), Constraints::default()))
            .collect(),
        bounds(),
        9,
    );
    climb.observe_all(
        &Proposal::plain(Origin::Explicit, starts.clone()),
        &observation(Some(score(1))),
    );
    let mut lengths: BTreeMap<usize, std::collections::BTreeSet<usize>> = BTreeMap::new();
    let start_keys = [int(1), int(4)];
    let mut key_moves = 0;
    for _ in 0..300 {
        let proposal = propose(&mut climb);
        // A key move keeps the map's size and its entries' values and changes one key; no other
        // move of one hole does (a value move keeps the keys, removal and insertion the size).
        if let Value::Map(entries) = &proposal.values[1]
            && entries.len() == start_keys.len()
            && entries.iter().map(|(key, _)| key).ne(start_keys.iter())
        {
            let mut values: Vec<&Value> = entries.iter().map(|(_, value)| value).collect();
            values.sort();
            assert_eq!(
                values,
                [&Value::Bool(false), &Value::Bool(true)],
                "{entries:?}"
            );
            let kept = entries
                .iter()
                .filter(|(key, _)| start_keys.contains(key))
                .count();
            assert_eq!(kept, 1, "one key moved: {entries:?}");
            key_moves += 1;
        }
        for (index, value) in proposal.values.iter().enumerate() {
            assert!(
                values::admissible(value, &sorts[index], &Constraints::default(), &bounds()),
                "{value:?}"
            );
            let length = match value {
                Value::Set(items) | Value::List(items) => items.len(),
                Value::Map(entries) => entries.len(),
                other => panic!("{other:?}"),
            };
            lengths.entry(index).or_default().insert(length);
        }
        climb.observe(&proposal, &observation(Some(score(2))), false);
    }
    assert!(key_moves > 0, "no proposal moved a map key");
    // Every collection both lost and gained an element in some proposal.
    for (index, start) in [2usize, 2, 1].iter().enumerate() {
        let seen = &lengths[&index];
        assert!(
            seen.contains(&(start - 1)) && seen.contains(&(start + 1)),
            "{index}: {seen:?}"
        );
    }
}

#[test]
fn integer_steps_land_on_a_range_end_and_mint_stays_in_width() {
    let ranged = Constraints {
        range: Some(IntRange {
            min: Some(BigInt::from(0)),
            max: Some(BigInt::from(10)),
        }),
        ..Constraints::default()
    };
    assert_eq!(step_int(&int(8), 4, true, &ranged), Some(int(10)));
    assert_eq!(step_int(&int(8), 4, false, &ranged), Some(int(0)));
    assert_eq!(
        step_int(&int(8), 0, true, &Constraints::default()),
        Some(int(9))
    );
    let mint = Value::MInt {
        width: 8,
        value: 250u32.into(),
    };
    assert_eq!(
        step_int(&mint, 4, true, &Constraints::default()),
        Some(Value::MInt {
            width: 8,
            value: 255u32.into()
        })
    );
}

#[test]
fn values_beyond_the_generator_bounds_are_not_admissible() {
    let small = GenerationBounds {
        int_bits: 8,
        length: 2,
        depth: 1,
    };
    let unconstrained = Constraints::default();
    assert!(values::admissible(
        &int(255),
        &ValueSort::Int,
        &unconstrained,
        &small
    ));
    assert!(!values::admissible(
        &int(256),
        &ValueSort::Int,
        &unconstrained,
        &small
    ));
    assert!(!values::admissible(
        &Value::String("abc".into()),
        &ValueSort::String,
        &unconstrained,
        &small
    ));
    assert!(values::admissible(
        &Value::String("ab".into()),
        &ValueSort::String,
        &unconstrained,
        &small
    ));
}

/// The comparison `left op right` of rule `r`, as the condition records give it.
fn compared(comparison: crate::score::distance::Comparison, left: i64, right: i64) -> Compared {
    Compared {
        rule: "r".into(),
        comparison,
        left: Operand::Int(left.into()),
        right: Operand::Int(right.into()),
    }
}

#[test]
fn the_incumbent_is_changed_from_its_pool_of_run_time_literals() {
    use crate::score::distance::Comparison;
    // Two holes; the guard compared the second hole's 7 with 4096 (`X >Int 4096`): the change
    // is 4097, which a climb of `±2^e` steps from 7 reaches only in many cases.
    let start = vec![int(1), int(7)];
    let mut found = 0;
    for seed in 0..8 {
        let mut climb = ClimbProposer::new(
            vec![
                hole(ValueSort::Int, Constraints::default()),
                hole(ValueSort::Int, Constraints::default()),
            ],
            bounds(),
            seed,
        );
        let mut seen = observation(Some(score(4090)));
        seen.comparisons = vec![compared(Comparison::IntGt, 7, 4096)];
        climb.observe_all(&Proposal::plain(Origin::Explicit, start.clone()), &seen);
        let proposals: Vec<Vec<Value>> = (0..8).map(|_| propose(&mut climb).values).collect();
        found += proposals
            .iter()
            .filter(|values| **values == [int(1), int(4097)])
            .count();
    }
    // A quarter of the proposals, give or take: 64 proposals over the seeds.
    assert!((4..=40).contains(&found), "{found}");
    // An incumbent without a pool never draws a run-time change; the moves' stream is the
    // same as with a pool whose values occur nowhere in the incumbent.
    let moves = |comparisons: Vec<Compared>| {
        let mut climb = ClimbProposer::new(
            vec![hole(ValueSort::Int, Constraints::default())],
            bounds(),
            3,
        );
        let mut seen = observation(Some(score(10)));
        seen.comparisons = comparisons;
        climb.observe_all(&Proposal::plain(Origin::Explicit, vec![int(5)]), &seen);
        (0..32)
            .map(|_| propose(&mut climb).values)
            .collect::<Vec<_>>()
    };
    assert_eq!(
        moves(Vec::new()),
        moves(vec![compared(Comparison::IntEq, 99, 100)])
    );
}
