//! Unit tests of the corpus proposer's corpus, mutations and admissibility, without a
//! definition: coverage and scores are given, not computed.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use rand_chacha::ChaCha20Rng;

use super::*;
use crate::{
    engine::proposer::{Observation, Origin, Proposal, ProposalContext, Proposer},
    exec::OutcomeClass,
    proposers::dictionary::Literal,
    score::{Distance, Guard, Level, Score},
    values::{CollectionSymbols, IntRange, LengthRange},
};

fn bounds() -> GenerationBounds {
    GenerationBounds {
        int_bits: 64,
        length: 8,
        depth: 4,
    }
}

fn hole(sort: ValueSort, constraints: Constraints) -> CorpusHole {
    let generator = Generator::new(&sort, &constraints, &bounds()).expect("a generator");
    CorpusHole {
        sort,
        constraints,
        generator,
    }
}

fn int(value: i64) -> Value {
    Value::Int(BigInt::from(value))
}

fn symbols(kore_sort: &str) -> CollectionSymbols {
    CollectionSymbols {
        kore_sort: kore_sort.into(),
        unit: "unit".into(),
        element: "element".into(),
        concat: "concat".into(),
        element_arguments: Vec::new(),
    }
}

fn list_of_ints() -> ValueSort {
    ValueSort::List {
        sort: "List".into(),
        symbols: symbols("SortList"),
        element: Box::new(ValueSort::Int),
        text: None,
    }
}

/// A harvest of `Int` literals, each at distance 0.
fn harvest(literals: &[i64]) -> Arc<Harvest> {
    Arc::new(Harvest::from_literals(
        literals
            .iter()
            .map(|value| {
                (
                    Literal::Domain {
                        sort: "SortInt{}".into(),
                        text: value.to_string().into_bytes(),
                    },
                    0,
                )
            })
            .collect::<BTreeMap<_, _>>(),
    ))
}

fn observation(class: OutcomeClass, applied: &[&str], score: Option<Score>) -> Observation {
    Observation {
        case: 0,
        class,
        applied: applied.iter().map(|rule| (*rule).to_owned()).collect(),
        matched: Vec::new(),
        work: 1,
        score,
        reads: Vec::new(),
        blocked: None,
    }
}

fn score(raw: u32) -> Score {
    Score {
        level: Level::At(0),
        guard: Guard::Defined(Distance::normalized(raw.into())),
    }
}

fn propose(corpus: &mut CorpusProposer) -> Proposal {
    let mut rng = ChaCha20Rng::from_seed([3; 32]);
    corpus
        .propose(&mut ProposalContext { rng: &mut rng })
        .expect("a corpus proposal")
}

#[test]
fn the_corpus_keeps_new_coverage_and_strictly_better_scores_of_miss_cases() {
    let mut corpus = CorpusProposer::new(
        vec![hole(ValueSort::Int, Constraints::default())],
        &harvest(&[]),
        bounds(),
        1,
    );
    assert!(!corpus.ready());
    assert_eq!(corpus.budget_share(), Some((1, 2)));
    let case = |value| Proposal::plain(Origin::Explicit, vec![int(value)]);
    // A case that is not a miss never enters, whatever its coverage.
    corpus.observe_all(&case(1), &observation(OutcomeClass::Stuck, &["a"], None));
    assert!(!corpus.ready());
    corpus.observe_all(&case(2), &observation(OutcomeClass::Miss, &["a"], None));
    assert!(corpus.ready());
    // The same coverage again: not kept.
    corpus.observe_all(&case(3), &observation(OutcomeClass::Miss, &["a"], None));
    // A rule no earlier miss reached, even beside known ones: kept.
    corpus.observe_all(
        &case(4),
        &observation(OutcomeClass::Miss, &["a", "b"], None),
    );
    // Scores: the first one, then only a strictly better one.
    let miss = |raw| observation(OutcomeClass::Miss, &["a"], Some(score(raw)));
    corpus.observe_all(&case(5), &miss(9));
    corpus.observe_all(&case(6), &miss(9));
    corpus.observe_all(&case(7), &miss(12));
    corpus.observe_all(&case(8), &miss(3));
    let kept: Vec<&[Value]> = corpus.entries();
    assert_eq!(
        kept,
        vec![&[int(2)][..], &[int(4)][..], &[int(5)][..], &[int(8)][..]]
    );
}

#[test]
fn a_full_corpus_drops_its_oldest_score_only_entry_first() {
    let mut corpus = CorpusProposer::new(
        vec![hole(ValueSort::Int, Constraints::default())],
        &harvest(&[]),
        bounds(),
        1,
    );
    let case = |value: usize| {
        Proposal::plain(
            Origin::Explicit,
            vec![int(i64::try_from(value).expect("small"))],
        )
    };
    corpus.observe_all(&case(0), &observation(OutcomeClass::Miss, &["r0"], None));
    // Entry 1 enters for its score alone.
    corpus.observe_all(
        &case(1),
        &observation(OutcomeClass::Miss, &["r0"], Some(score(5))),
    );
    for index in 2..=MAX_ENTRIES {
        let rule = format!("r{index}");
        corpus.observe_all(
            &case(index),
            &observation(OutcomeClass::Miss, &[rule.as_str()], None),
        );
    }
    let kept = corpus.entries();
    assert_eq!(kept.len(), MAX_ENTRIES);
    assert_eq!(kept[0], &[int(0)][..]);
    assert_eq!(kept[1], &[int(2)][..], "the score-only entry went first");
    assert_eq!(kept[MAX_ENTRIES - 1], &[int(256)][..]);
    // With no score-only entry left, the oldest goes.
    let rule = format!("r{}", MAX_ENTRIES + 1);
    corpus.observe_all(
        &case(MAX_ENTRIES + 1),
        &observation(OutcomeClass::Miss, &[rule.as_str()], None),
    );
    assert_eq!(corpus.entries()[0], &[int(2)][..]);
}

#[test]
fn every_proposal_is_admissible_and_changes_the_entry() {
    let set = ValueSort::Set {
        sort: "Set".into(),
        symbols: symbols("SortSet"),
        element: Box::new(ValueSort::Int),
        text: None,
    };
    let map = ValueSort::Map {
        sort: "Map".into(),
        symbols: symbols("SortMap"),
        key: Box::new(ValueSort::Int),
        value: Box::new(ValueSort::Bool),
        text: None,
    };
    let ranged = Constraints {
        range: Some(IntRange {
            min: Some(BigInt::from(-5)),
            max: Some(BigInt::from(5)),
        }),
        ..Constraints::default()
    };
    let short = Constraints {
        length: Some(LengthRange {
            min: Some(1),
            max: Some(3),
        }),
        ..Constraints::default()
    };
    let choices = Constraints {
        choices: Some(vec![int(10), int(20), int(30)]),
        ..Constraints::default()
    };
    let holes = vec![
        hole(ValueSort::Int, ranged),
        hole(ValueSort::Bool, Constraints::default()),
        hole(ValueSort::String, Constraints::default()),
        hole(list_of_ints(), short),
        hole(set, Constraints::default()),
        hole(map, Constraints::default()),
        hole(ValueSort::Int, choices),
    ];
    let start = vec![
        int(0),
        Value::Bool(false),
        Value::String("ab".into()),
        Value::List(vec![int(1)]),
        Value::Set(vec![int(1), int(2)]),
        Value::Map(vec![(int(1), Value::Bool(true))]),
        int(20),
    ];
    let sorts: Vec<(ValueSort, Constraints)> = holes
        .iter()
        .map(|hole| (hole.sort.clone(), hole.constraints.clone()))
        .collect();
    let mut corpus = CorpusProposer::new(holes, &harvest(&[3, 7, 100]), bounds(), 5);
    corpus.observe_all(
        &Proposal::plain(Origin::Explicit, start.clone()),
        &observation(OutcomeClass::Miss, &["a"], None),
    );
    let mut changed = vec![false; start.len()];
    for _ in 0..400 {
        let proposal = propose(&mut corpus);
        assert_eq!(proposal.origin, Origin::Scheduled(ProposerKind::Corpus));
        assert_eq!(proposal.values.len(), start.len());
        let differing = proposal
            .values
            .iter()
            .zip(&start)
            .filter(|(new, old)| new != old)
            .count();
        assert!((1..=2).contains(&differing), "{:?}", proposal.values);
        for (index, ((value, (sort, constraints)), old)) in
            proposal.values.iter().zip(&sorts).zip(&start).enumerate()
        {
            assert!(
                values::admissible(value, sort, constraints, &bounds()),
                "hole {index}: {value:?}"
            );
            changed[index] |= value != old;
        }
    }
    assert!(changed.iter().all(|changed| *changed), "{changed:?}");
}

#[test]
fn harvested_literals_reach_list_elements_and_the_same_seed_proposes_the_same() {
    let run = |seed| {
        let mut corpus = CorpusProposer::new(
            vec![hole(list_of_ints(), Constraints::default())],
            &harvest(&[31_337]),
            bounds(),
            seed,
        );
        corpus.observe_all(
            &Proposal::plain(Origin::Explicit, vec![Value::List(vec![int(0)])]),
            &observation(OutcomeClass::Miss, &["a"], None),
        );
        (0..64)
            .map(|_| propose(&mut corpus).values)
            .collect::<Vec<_>>()
    };
    let first = run(11);
    assert_eq!(first, run(11));
    assert_ne!(first, run(12));
    let holds = |values: &Vec<Value>, wanted: i64| matches!(&values[0], Value::List(items) if items.contains(&int(wanted)));
    assert!(
        first.iter().any(|values| holds(values, 31_337)),
        "{first:?}"
    );
}

/// The lock of `tests/data/lock/lock.k` as a function of the list: the rules a run applies and
/// matches, as k-rust's coverage reports them on the lock, and the phase it ends in.
fn lock(keys: &[Value]) -> (Vec<String>, Vec<String>, usize) {
    let guards: [fn(i64) -> bool; 5] = [
        |x| x == 17,
        |x| x > 1000 && x < 1100,
        |x| x == 31_337,
        |x| x < -5000 && x > -5100,
        |x| x == 4242,
    ];
    let (mut applied, mut matched) = (vec!["begin".to_owned()], Vec::new());
    let mut phase = 0;
    for key in keys {
        if phase == guards.len() {
            break;
        }
        matched.push(format!("l{}", phase + 1));
        let passes = match key {
            Value::Int(number) => i64::try_from(number).is_ok_and(|x| guards[phase](x)),
            _ => false,
        };
        if !passes {
            break;
        }
        applied.push(format!("l{}", phase + 1));
        phase += 1;
    }
    applied.push("jam".to_owned());
    (applied, matched, phase)
}

#[test]
fn the_corpus_alone_opens_the_lock_model_one_key_at_a_time() {
    // Without a definition: the corpus proposes every case after the anchor, and each case's
    // coverage is the lock's. Blind sampling would need about 10^13 cases for the fifth key.
    let mut corpus = CorpusProposer::new(
        vec![hole(list_of_ints(), Constraints::default())],
        &harvest(&[17, 1000, 1100, 31_337, -5000, -5100, 4242]),
        bounds(),
        2,
    );
    let mut proposal = Proposal::plain(Origin::Explicit, vec![Value::List(vec![int(0)])]);
    let mut cases = 0;
    loop {
        cases += 1;
        let Value::List(keys) = &proposal.values[0] else {
            panic!("a list")
        };
        let (applied, matched, phase) = lock(keys);
        if phase == 5 {
            break;
        }
        assert!(cases < 3000, "the lock stayed shut after {cases} cases");
        let mut seen = observation(OutcomeClass::Miss, &[], None);
        seen.applied = applied;
        seen.matched = matched;
        corpus.observe_all(&proposal, &seen);
        proposal = propose(&mut corpus);
    }
    assert!(cases > 5, "{cases}");
}

#[test]
fn a_record_inside_a_list_changes_one_field_at_a_time() {
    // LEDGER's `Tx ::= transfer(Int, Int) | noop`, as the elements of a `List` hole.
    let tx = values::ledger_sort("Tx");
    let list = ValueSort::List {
        sort: "List".into(),
        symbols: symbols("SortList"),
        element: Box::new(tx.clone()),
        text: None,
    };
    let generator = Generator::new(&tx, &Constraints::default(), &bounds()).expect("a generator");
    let mut rng = ValueRng::from_seed([5; 32]);
    let symbol = loop {
        if let Value::Apply { symbol, arguments } =
            generator.try_generate(&mut rng).expect("a draw").current()
            && arguments.len() == 2
        {
            break symbol;
        }
    };
    let transfer = |amount: i64, fee: i64| Value::Apply {
        symbol: symbol.clone(),
        arguments: vec![int(amount), int(fee)],
    };
    let start = vec![
        transfer(123_456_789, 987_654_321),
        transfer(555_555_555, 444_444_444),
    ];
    let mut corpus = CorpusProposer::new(
        vec![hole(list.clone(), Constraints::default())],
        &harvest(&[]),
        bounds(),
        8,
    );
    corpus.observe_all(
        &Proposal::plain(Origin::Explicit, vec![Value::List(start.clone())]),
        &observation(OutcomeClass::Miss, &["a"], None),
    );
    let mut one_field = 0;
    for _ in 0..400 {
        let proposal = propose(&mut corpus);
        assert!(
            values::admissible(
                &proposal.values[0],
                &list,
                &Constraints::default(),
                &bounds()
            ),
            "{:?}",
            proposal.values[0]
        );
        let Value::List(items) = &proposal.values[0] else {
            panic!("a list")
        };
        if items.len() != start.len() {
            continue;
        }
        let changed: Vec<(&Value, &Value)> = items
            .iter()
            .zip(&start)
            .filter(|(new, old)| new != old)
            .collect();
        if let [
            (
                Value::Apply {
                    symbol: new,
                    arguments: after,
                },
                Value::Apply {
                    arguments: before, ..
                },
            ),
        ] = changed[..]
            && *new == symbol
            && after.iter().zip(before).filter(|(a, b)| a != b).count() == 1
        {
            one_field += 1;
        }
    }
    assert!(
        one_field >= 10,
        "{one_field} proposals changed one field of one record"
    );
}
