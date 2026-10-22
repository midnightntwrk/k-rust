use rand::SeedableRng as _;

use super::*;

fn int(value: i64) -> Value {
    Value::Int(value.into())
}

fn tx(nonce: i64, amount: i64) -> Value {
    Value::Apply {
        symbol: "Lbltx".into(),
        arguments: vec![int(nonce), int(amount)],
    }
}

fn compared(comparison: Comparison, left: i64, right: i64) -> Compared {
    Compared {
        rule: "r".into(),
        comparison,
        left: Operand::Int(left.into()),
        right: Operand::Int(right.into()),
    }
}

fn rng() -> ChaCha20Rng {
    ChaCha20Rng::from_seed([7; 32])
}

/// Every candidate change of `values`, as the hole values it gives.
fn changes(values: &[Value], comparisons: &[Compared]) -> Vec<Vec<Value>> {
    candidates(values, comparisons)
        .into_iter()
        .filter_map(|candidate| {
            let mut changed = values.to_vec();
            changed[candidate.hole] = replace(
                &values[candidate.hole],
                &candidate.from,
                candidate.occurrence,
                &candidate.to,
                &mut 0,
            )?;
            Some(changed)
        })
        .collect()
}

#[test]
fn the_value_taken_is_the_nearest_that_passes_the_comparison() {
    use Comparison as C;
    // `x op 10` with x = 3 on the left, and `20 op y` with y = 3 on the right.
    let cases = [
        (C::IntEq, 10, 20),
        (C::IntLe, 10, 20),
        (C::IntGe, 10, 20),
        (C::IntLt, 9, 21),
        (C::IntGt, 11, 19),
        (C::IntNe, 11, 21),
    ];
    for (comparison, left_value, right_value) in cases {
        assert_eq!(
            changes(&[int(3)], &[compared(comparison, 3, 10)]),
            vec![vec![int(left_value)]],
            "{comparison:?}, left"
        );
        assert_eq!(
            changes(&[int(3)], &[compared(comparison, 20, 3)]),
            vec![vec![int(right_value)]],
            "{comparison:?}, right"
        );
    }
}

#[test]
fn a_compared_value_is_replaced_where_it_occurs_at_any_depth() {
    // The ledger: the third transaction's amount 7 was compared with the balance 400.
    let values = vec![Value::List(vec![tx(0, 100), tx(1, 200), tx(2, 7)]), int(5)];
    let pool = [compared(Comparison::IntEq, 7, 400)];
    assert_eq!(
        changes(&values, &pool),
        vec![vec![
            Value::List(vec![tx(0, 100), tx(1, 200), tx(2, 400)]),
            int(5),
        ]]
    );
    let proposal = propose(&values, &pool, &mut rng(), |_, _| true).expect("a change");
    assert_eq!(
        proposal[0],
        Value::List(vec![tx(0, 100), tx(1, 200), tx(2, 400)])
    );
    // Every occurrence is a candidate, a coincidental one too; the proposer's check refuses
    // the changes it does not admit.
    let twice = vec![Value::List(vec![tx(7, 1), tx(1, 7)])];
    assert_eq!(changes(&twice, &pool).len(), 2);
    assert_eq!(propose(&twice, &pool, &mut rng(), |_, _| false), None);
    // A map's keys and values, and a set's elements, are searched too.
    let map = vec![Value::Map(vec![(int(2), int(7)), (int(7), int(1))])];
    assert_eq!(
        changes(&map, &pool),
        vec![
            vec![Value::Map(vec![(int(2), int(400)), (int(7), int(1))])],
            vec![Value::Map(vec![(int(2), int(7)), (int(400), int(1))])],
        ]
    );
}

#[test]
fn a_change_that_merges_set_elements_or_map_keys_is_not_proposed() {
    let pool = [compared(Comparison::IntEq, 1, 2)];
    let set = vec![Value::Set(vec![int(1), int(2)])];
    assert_eq!(changes(&set, &pool), Vec::<Vec<Value>>::new());
    assert_eq!(propose(&set, &pool, &mut rng(), |_, _| true), None);
    let keys = vec![Value::Map(vec![(int(1), int(0)), (int(2), int(0))])];
    assert_eq!(changes(&keys, &pool), Vec::<Vec<Value>>::new());
}

#[test]
fn strings_take_the_other_string_of_an_equality_only() {
    let strings = |comparison| Compared {
        rule: "r".into(),
        comparison,
        left: Operand::Str("opne".into()),
        right: Operand::Str("open".into()),
    };
    let values = vec![Value::String("opne".into())];
    assert_eq!(
        changes(&values, &[strings(Comparison::StrEq)]),
        vec![vec![Value::String("open".into())]]
    );
    assert!(changes(&values, &[strings(Comparison::StrNe)]).is_empty());
    // An integer and a string with the same digits are different values.
    assert!(
        changes(
            &[Value::String("7".into())],
            &[compared(Comparison::IntEq, 7, 8)]
        )
        .is_empty()
    );
}

#[test]
fn a_pool_without_candidates_draws_nothing() {
    let mut drawn = rng();
    // No hole holds a compared value: no candidate, and the stream is untouched.
    let values = vec![int(1)];
    assert_eq!(
        propose(
            &values,
            &[compared(Comparison::IntEq, 5, 6)],
            &mut drawn,
            |_, _| true
        ),
        None
    );
    assert_eq!(propose(&values, &[], &mut drawn, |_, _| true), None);
    let mut fresh = rng();
    assert_eq!(drawn.random::<u64>(), fresh.random::<u64>());
}

#[test]
fn candidates_are_bounded_and_listed_once() {
    // The same comparison twice gives each candidate once.
    let pool = [
        compared(Comparison::IntEq, 3, 4),
        compared(Comparison::IntEq, 3, 4),
    ];
    assert_eq!(candidates(&[int(3)], &pool).len(), 1);
    let many = vec![Value::List((0..300).map(|_| int(3)).collect())];
    assert_eq!(candidates(&many, &pool).len(), MAX_CANDIDATES);
}
