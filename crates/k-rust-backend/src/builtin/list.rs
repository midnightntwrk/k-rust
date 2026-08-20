//! Concrete `LIST` hooks implemented by Booster.

use std::sync::Arc;

use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

use super::{
    BuiltinError, BuiltinResult, bool_term, expect_arity, expect_sort, int_term, read_int,
};
use crate::term::{CollectionSymbols, ListDefinition, Sort, Term, TermKind};

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    let result = match hook {
        "LIST.concat" => concat(arguments),
        "LIST.element" => element(arguments),
        "LIST.in" => contains(arguments),
        "LIST.size" => size(arguments),
        "LIST.unit" => unit(arguments),
        _ => Ok(None),
    }?;
    match hook {
        "LIST.get" => get(arguments),
        "LIST.make" => make(arguments),
        "LIST.range" => range(arguments),
        "LIST.update" => update(arguments),
        "LIST.updateAll" => update_all(arguments),
        _ => Ok(result.into()),
    }
}

pub(super) fn k_item_definition() -> Arc<ListDefinition> {
    Arc::new(ListDefinition {
        symbols: CollectionSymbols {
            unit: "Lbl'Stop'List".into(),
            element: "LblListItem".into(),
            concat: "Lbl'Unds'List'Unds'".into(),
        },
        element_sort: "SortKItem".into(),
        list_sort: "SortList".into(),
    })
}

fn concat(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("LIST.concat", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    match (left.kind(), right.kind()) {
        (
            TermKind::List {
                definition: left_definition,
                heads: left_heads,
                rest: left_rest,
            },
            TermKind::List {
                definition: right_definition,
                heads: right_heads,
                rest: right_rest,
            },
        ) => {
            if left_definition != right_definition {
                return Ok(None);
            }
            let result = match (left_rest, right_rest) {
                (None, None) => {
                    let mut heads = left_heads.clone();
                    heads.extend(right_heads.iter().cloned());
                    Term::list(left_definition.clone(), heads, None)
                }
                (None, Some(rest)) => {
                    let mut heads = left_heads.clone();
                    heads.extend(right_heads.iter().cloned());
                    Term::list(left_definition.clone(), heads, Some(rest.clone()))
                }
                (Some((middle, tails)), None) => {
                    let mut tails = tails.clone();
                    tails.extend(right_heads.iter().cloned());
                    Term::list(
                        left_definition.clone(),
                        left_heads.clone(),
                        Some((middle.clone(), tails)),
                    )
                }
                (Some(_), Some(_)) => return Ok(None),
            };
            Ok(Some(result))
        }
        (
            TermKind::List {
                definition,
                heads,
                rest: None,
            },
            _,
        ) => Ok(Some(Term::list(
            definition.clone(),
            heads.clone(),
            Some((right.clone(), Vec::new())),
        ))),
        (
            _,
            TermKind::List {
                definition,
                heads,
                rest: None,
            },
        ) => Ok(Some(Term::list(
            definition.clone(),
            Vec::new(),
            Some((left.clone(), heads.clone())),
        ))),
        _ => Ok(None),
    }
}

fn element(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("LIST.element", arguments, 1)?;
    Ok(Some(Term::list(
        k_item_definition(),
        vec![arguments[0].clone()],
        None,
    )))
}

fn get(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("LIST.get", arguments, 2)?;
    let [list, index] = arguments else {
        unreachable!()
    };
    let TermKind::List { heads, rest, .. } = list.kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if heads.is_empty() && rest.is_none() {
        return Ok(BuiltinResult::Bottom);
    }
    let Some(index_value) = read_int(index) else {
        expect_sort("LIST.get", index, &Sort::simple("SortInt"))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    if index_value.sign() != Sign::Minus {
        return Ok(index_value
            .to_usize()
            .and_then(|index| heads.get(index).cloned())
            .map(BuiltinResult::Value)
            .unwrap_or_else(|| {
                if rest.is_none() {
                    BuiltinResult::Bottom
                } else {
                    BuiltinResult::NotApplicable
                }
            }));
    }
    let Some(distance) = (-index_value).to_usize() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let known_tail = match rest {
        None => heads,
        Some((_, tails)) => tails,
    };
    Ok(distance
        .checked_sub(1)
        .and_then(|offset| known_tail.len().checked_sub(offset + 1))
        .and_then(|index| known_tail.get(index).cloned())
        .map(BuiltinResult::Value)
        .unwrap_or_else(|| {
            if rest.is_none() {
                BuiltinResult::Bottom
            } else {
                BuiltinResult::NotApplicable
            }
        }))
}

fn contains(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("LIST.in", arguments, 2)?;
    let [element, list] = arguments else {
        unreachable!()
    };
    let TermKind::List { heads, rest, .. } = list.kind() else {
        return Ok(None);
    };
    match rest {
        None if heads.contains(element) => Ok(Some(bool_term(true))),
        None if element.attributes().constructor_like
            && heads.iter().all(|head| head.attributes().constructor_like) =>
        {
            Ok(Some(bool_term(false)))
        }
        Some((_, tails)) if tails.contains(element) => Ok(Some(bool_term(true))),
        _ => Ok(None),
    }
}

fn make(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("LIST.make", arguments, 2)?;
    let [length, value] = arguments else {
        unreachable!()
    };
    let Some(length) = read_int(length) else {
        expect_sort("LIST.make", length, &Sort::simple("SortInt"))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    if length.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let Some(length) = length.to_usize() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(Term::list(
        k_item_definition(),
        vec![value.clone(); length],
        None,
    )))
}

fn range(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("LIST.range", arguments, 3)?;
    let [list, from_front, from_back] = arguments else {
        unreachable!()
    };
    let TermKind::List {
        definition,
        heads,
        rest,
    } = list.kind()
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(front) = read_int(from_front) else {
        expect_sort("LIST.range", from_front, &Sort::simple("SortInt"))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(back) = read_int(from_back) else {
        expect_sort("LIST.range", from_back, &Sort::simple("SortInt"))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    if front.sign() == Sign::Minus || back.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let front = front.to_usize();
    let back = back.to_usize();
    match rest {
        None => {
            let (Some(front), Some(back)) = (front, back) else {
                return Ok(BuiltinResult::NotApplicable);
            };
            let Some(end) = heads.len().checked_sub(back) else {
                return Ok(BuiltinResult::Bottom);
            };
            if front > end {
                return Ok(BuiltinResult::Bottom);
            }
            Ok(BuiltinResult::Value(Term::list(
                definition.clone(),
                heads[front..end].to_vec(),
                None,
            )))
        }
        Some((middle, tails)) => {
            let (Some(front), Some(back)) = (front, back) else {
                return Ok(BuiltinResult::NotApplicable);
            };
            if front > heads.len() || back > tails.len() {
                return Ok(BuiltinResult::NotApplicable);
            };
            let tail_end = tails.len() - back;
            Ok(BuiltinResult::Value(Term::list(
                definition.clone(),
                heads[front..].to_vec(),
                Some((middle.clone(), tails[..tail_end].to_vec())),
            )))
        }
    }
}

fn size(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("LIST.size", arguments, 1)?;
    let TermKind::List {
        heads, rest: None, ..
    } = arguments[0].kind()
    else {
        return Ok(None);
    };
    Ok(Some(int_term(BigInt::from(heads.len()))))
}

fn unit(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("LIST.unit", arguments, 0)?;
    Ok(Some(Term::list(k_item_definition(), Vec::new(), None)))
}

fn update(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("LIST.update", arguments, 3)?;
    let [list, index, value] = arguments else {
        unreachable!()
    };
    let TermKind::List {
        definition,
        heads,
        rest,
    } = list.kind()
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(index) = read_int(index) else {
        expect_sort("LIST.update", index, &Sort::simple("SortInt"))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    if index.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let Some(index) = index.to_usize() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if index >= heads.len() {
        return Ok(if rest.is_none() {
            BuiltinResult::Bottom
        } else {
            BuiltinResult::NotApplicable
        });
    }
    let mut updated = heads.clone();
    updated[index] = value.clone();
    Ok(BuiltinResult::Value(Term::list(
        definition.clone(),
        updated,
        rest.clone(),
    )))
}

fn update_all(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("LIST.updateAll", arguments, 3)?;
    let [original, index, updates] = arguments else {
        unreachable!()
    };
    let (
        TermKind::List {
            definition,
            heads: original,
            rest: None,
        },
        TermKind::List {
            definition: update_definition,
            heads: updates,
            rest: None,
        },
    ) = (original.kind(), updates.kind())
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if definition != update_definition {
        return Ok(BuiltinResult::NotApplicable);
    }
    let Some(index) = read_int(index) else {
        expect_sort("LIST.updateAll", index, &Sort::simple("SortInt"))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    if index.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let Some(index) = index.to_usize() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(end) = index.checked_add(updates.len()) else {
        return Ok(BuiltinResult::Bottom);
    };
    if end > original.len() {
        return Ok(BuiltinResult::Bottom);
    }
    let mut result = original.clone();
    result.splice(index..end, updates.iter().cloned());
    Ok(BuiltinResult::Value(Term::list(
        definition.clone(),
        result,
        None,
    )))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Variable;

    fn definition() -> Arc<ListDefinition> {
        Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: "unit".into(),
                element: "element".into(),
                concat: "concat".into(),
            },
            element_sort: "SortItem".into(),
            list_sort: "SortItems".into(),
        })
    }

    fn item(value: &str) -> Term {
        Term::domain_value(Sort::simple("SortItem"), value)
    }

    fn integer(value: i64) -> Term {
        int_term(BigInt::from(value))
    }

    #[test]
    fn get_indexes_complete_lists_from_both_ends() {
        let list = Term::list(definition(), vec![item("a"), item("b"), item("c")], None);

        assert_eq!(
            get(&[list.clone(), integer(1)]),
            Ok(BuiltinResult::Value(item("b")))
        );
        assert_eq!(
            get(&[list.clone(), integer(-1)]),
            Ok(BuiltinResult::Value(item("c")))
        );
        assert_eq!(
            get(&[list, integer(-3)]),
            Ok(BuiltinResult::Value(item("a")))
        );
    }

    #[test]
    fn get_uses_only_the_known_ends_of_an_opaque_list() {
        let middle = Term::variable(Variable::new("REST", Sort::simple("SortItems")));
        let list = Term::list(
            definition(),
            vec![item("a")],
            Some((middle, vec![item("b"), item("c")])),
        );

        assert_eq!(
            get(&[list.clone(), integer(0)]),
            Ok(BuiltinResult::Value(item("a")))
        );
        assert_eq!(
            get(&[list.clone(), integer(1)]),
            Ok(BuiltinResult::NotApplicable)
        );
        assert_eq!(
            get(&[list.clone(), integer(-1)]),
            Ok(BuiltinResult::Value(item("c")))
        );
        assert_eq!(get(&[list, integer(-3)]), Ok(BuiltinResult::NotApplicable));
    }

    #[test]
    fn range_preserves_an_opaque_middle_when_the_drops_are_known() {
        let middle = Term::variable(Variable::new("REST", Sort::simple("SortItems")));
        let list = Term::list(
            definition(),
            vec![item("a"), item("b")],
            Some((middle.clone(), vec![item("c"), item("d")])),
        );
        let expected = Term::list(
            definition(),
            vec![item("b")],
            Some((middle, vec![item("c")])),
        );

        assert_eq!(
            range(&[list, integer(1), integer(1)]),
            Ok(BuiltinResult::Value(expected))
        );
    }

    #[test]
    fn membership_is_false_only_for_a_fully_known_constructor_list() {
        let concrete = Term::list(definition(), vec![item("a")], None);
        let unknown = Term::variable(Variable::new("X", Sort::simple("SortItem")));

        assert_eq!(
            contains(&[item("b"), concrete.clone()]),
            Ok(Some(bool_term(false)))
        );
        assert_eq!(contains(&[unknown, concrete]), Ok(None));
    }

    #[test]
    fn default_list_hooks_use_the_reference_kitem_definition() {
        let BuiltinResult::Value(made) = make(&[integer(2), item("x")]).unwrap() else {
            panic!("LIST.make should evaluate")
        };
        let TermKind::List {
            definition,
            heads,
            rest,
        } = made.kind()
        else {
            panic!("LIST.make should produce an internal list")
        };

        assert_eq!(definition.as_ref(), k_item_definition().as_ref());
        assert_eq!(heads, &[item("x"), item("x")]);
        assert!(rest.is_none());
    }

    #[test]
    fn concat_update_and_size_cover_the_remaining_list_operations() {
        let definition = definition();
        let left = Term::list(definition.clone(), vec![item("a")], None);
        let right = Term::list(definition.clone(), vec![item("b"), item("c")], None);
        let joined = Term::list(
            definition.clone(),
            vec![item("a"), item("b"), item("c")],
            None,
        );
        let changed = Term::list(definition, vec![item("a"), item("x"), item("c")], None);

        assert_eq!(concat(&[left, right]), Ok(Some(joined.clone())));
        assert_eq!(
            update(&[joined.clone(), integer(1), item("x")]),
            Ok(BuiltinResult::Value(changed))
        );
        assert_eq!(size(&[joined]), Ok(Some(integer(3))));
    }

    #[test]
    fn concat_is_indeterminate_with_two_opaque_middles() {
        let definition = definition();
        let left_rest = Term::variable(Variable::new("LEFT", Sort::simple("SortItems")));
        let right_rest = Term::variable(Variable::new("RIGHT", Sort::simple("SortItems")));
        let left = Term::list(
            definition.clone(),
            vec![item("a")],
            Some((left_rest, vec![item("b")])),
        );
        let right = Term::list(
            definition,
            vec![item("c")],
            Some((right_rest, vec![item("d")])),
        );

        assert_eq!(concat(&[left, right]), Ok(None));
    }

    #[test]
    fn partial_list_hooks_return_bottom_for_undefined_inputs() {
        let definition = definition();
        let list = Term::list(definition.clone(), vec![item("a"), item("b")], None);
        let replacement = Term::list(definition, vec![item("x"), item("y")], None);

        assert_eq!(get(&[list.clone(), integer(2)]), Ok(BuiltinResult::Bottom));
        assert_eq!(
            update(&[list.clone(), integer(-1), item("x")]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            update_all(&[list.clone(), integer(1), replacement]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            range(&[list, integer(2), integer(1)]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(make(&[integer(-1), item("x")]), Ok(BuiltinResult::Bottom));
    }
}
