//! Concrete `LIST` hooks implemented by Booster: per-call operations on the internal list
//! representation; a responsibility, not an algorithm; no counter of its own, no worklist.

use std::sync::Arc;

use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

use k_rust_kore::names::BuiltinSort;

use super::{
    BuiltinResult, HookResult, MAX_LIST_RESULT_LEN, TARGET_RESULT_BYTES, UnsupportedHookReason,
    bool_term, describe_int, expect_arity, expect_sort, int_term, read_int, values_differ,
};
use crate::{
    matching::SortGraph,
    term::{CollectionSymbols, ListDefinition, Sort, Term, TermKind},
};

pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    sorts: Option<&SortGraph>,
) -> HookResult<BuiltinResult> {
    let result = match hook {
        "LIST.concat" => concat(arguments),
        "LIST.element" => element(arguments),
        "LIST.in" => contains(arguments, sorts),
        "LIST.size" => size(arguments),
        "LIST.unit" => unit(arguments),
        "LIST.get" => return get(arguments),
        "LIST.make" => return make(arguments),
        "LIST.range" => return range(arguments),
        "LIST.update" => return update(arguments),
        "LIST.updateAll" => return update_all(arguments),
        _ => {
            return Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::NotImplemented,
            ));
        }
    }?;
    Ok(result.into())
}

pub(super) fn k_item_definition() -> Arc<ListDefinition> {
    Arc::new(ListDefinition {
        symbols: CollectionSymbols {
            unit: "Lbl'Stop'List".into(),
            element: "LblListItem".into(),
            concat: "Lbl'Unds'List'Unds'".into(),
        },
        element_sort: BuiltinSort::KItem.kore_name().into(),
        list_sort: BuiltinSort::List.kore_name().into(),
    })
}

fn concat(arguments: &[Term]) -> HookResult<Option<Term>> {
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

fn element(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("LIST.element", arguments, 1)?;
    Ok(Some(Term::list(
        k_item_definition(),
        vec![arguments[0].clone()],
        None,
    )))
}

fn get(arguments: &[Term]) -> HookResult<BuiltinResult> {
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
        expect_sort("LIST.get", index, &Sort::builtin(BuiltinSort::Int))?;
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
        return Ok(if rest.is_none() {
            BuiltinResult::Bottom
        } else {
            BuiltinResult::NotApplicable
        });
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

fn contains(arguments: &[Term], sorts: Option<&SortGraph>) -> HookResult<Option<Term>> {
    expect_arity("LIST.in", arguments, 2)?;
    let [element, list] = arguments else {
        unreachable!()
    };
    let TermKind::List { heads, rest, .. } = list.kind() else {
        return Ok(None);
    };
    match rest {
        None if heads.contains(element) => Ok(Some(bool_term(true))),
        None if heads.iter().all(|head| values_differ(sorts, element, head)) => {
            Ok(Some(bool_term(false)))
        }
        Some((_, tails)) if tails.contains(element) => Ok(Some(bool_term(true))),
        _ => Ok(None),
    }
}

fn make(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("LIST.make", arguments, 2)?;
    let [length, value] = arguments else {
        unreachable!()
    };
    let Some(length) = read_int(length) else {
        expect_sort("LIST.make", length, &Sort::builtin(BuiltinSort::Int))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    if length.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let concrete_length = match bounded_list_length(&length) {
        Ok(length) => length,
        Err(reason) => return Ok(BuiltinResult::Unsupported(reason)),
    };
    Ok(BuiltinResult::Value(Term::list(
        k_item_definition(),
        vec![value.clone(); concrete_length],
        None,
    )))
}

/// A nonnegative `makeList` length as a number of elements, or `ResultTooLarge` above
/// [`list_length_limit`] on this target: the list exists, and the backend does not build it.
/// The arguments, a length and one element, are small, so the bound is the floor.
fn bounded_list_length(length: &BigInt) -> Result<usize, UnsupportedHookReason> {
    debug_assert!(
        length.sign() != Sign::Minus,
        "makeList of a negative length is undefined, checked by the caller"
    );
    let limit = list_length_limit(TARGET_RESULT_BYTES, size_of::<Term>() as u64);
    length
        .to_u64()
        .filter(|length| *length <= limit)
        .and_then(|length| usize::try_from(length).ok())
        .ok_or_else(|| UnsupportedHookReason::ResultTooLarge {
            detail: format!(
                "a List result of length {} needs more than {limit} elements",
                describe_int(length)
            ),
        })
}

/// The longest `makeList` result on a target where one result may take at most `target` bytes
/// ([`TARGET_RESULT_BYTES`]) and an element, one term reference, takes `reference` bytes:
/// [`MAX_LIST_RESULT_LEN`], and at most `target / reference`.
const fn list_length_limit(target: u64, reference: u64) -> u64 {
    let references = target / reference;
    if MAX_LIST_RESULT_LEN < references {
        MAX_LIST_RESULT_LEN
    } else {
        references
    }
}

fn range(arguments: &[Term]) -> HookResult<BuiltinResult> {
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
        expect_sort("LIST.range", from_front, &Sort::builtin(BuiltinSort::Int))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(back) = read_int(from_back) else {
        expect_sort("LIST.range", from_back, &Sort::builtin(BuiltinSort::Int))?;
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
                return Ok(BuiltinResult::Bottom);
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

fn size(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("LIST.size", arguments, 1)?;
    let TermKind::List {
        heads, rest: None, ..
    } = arguments[0].kind()
    else {
        return Ok(None);
    };
    Ok(Some(int_term(BigInt::from(heads.len()))))
}

fn unit(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("LIST.unit", arguments, 0)?;
    Ok(Some(Term::list(k_item_definition(), Vec::new(), None)))
}

fn update(arguments: &[Term]) -> HookResult<BuiltinResult> {
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
        expect_sort("LIST.update", index, &Sort::builtin(BuiltinSort::Int))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    if index.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let Some(index) = index.to_usize() else {
        return Ok(if rest.is_none() {
            BuiltinResult::Bottom
        } else {
            BuiltinResult::NotApplicable
        });
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

fn update_all(arguments: &[Term]) -> HookResult<BuiltinResult> {
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
        expect_sort("LIST.updateAll", index, &Sort::builtin(BuiltinSort::Int))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    if index.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let Some(index) = index.to_usize() else {
        return Ok(BuiltinResult::Bottom);
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
    use crate::builtin::target_result_bytes;
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
    fn fu17_list_membership_separates_symbolic_elements() {
        let int = Sort::simple("SortInt");
        let element_sort = Sort::simple("SortItem");
        let application = |name, variable| {
            Term::application(
                Arc::new(crate::term::Symbol::constructor(
                    name,
                    vec![int.clone()],
                    element_sort.clone(),
                )),
                Vec::new(),
                vec![Term::variable(Variable::new(variable, int.clone()))],
            )
        };
        let a = application("a", "A");
        let b = application("b", "B");
        let collection = Term::list(definition(), vec![a.clone()], None);
        assert_eq!(
            super::super::evaluate_hook("LIST.in", &[b.clone(), collection.clone()])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(bool_term(false))
        );
        assert_eq!(
            super::super::evaluate_hook("LIST.in", &[a.clone(), collection.clone()])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(bool_term(true))
        );
        let open = Term::list(
            definition(),
            vec![a.clone()],
            Some((
                Term::variable(Variable::new("REST", Sort::simple("SortItems"))),
                Vec::new(),
            )),
        );
        assert_eq!(
            super::super::evaluate_hook("LIST.in", &[b, open])
                .unwrap()
                .unwrap(),
            BuiltinResult::NotApplicable,
        );
        let variable = Term::variable(Variable::new("C", element_sort));
        assert_eq!(
            super::super::evaluate_hook("LIST.in", &[variable, collection])
                .unwrap()
                .unwrap(),
            BuiltinResult::NotApplicable
        );
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
            contains(&[item("b"), concrete.clone()], None),
            Ok(Some(bool_term(false)))
        );
        assert_eq!(contains(&[unknown, concrete], None), Ok(None));
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

    #[test]
    fn make_length_above_usize_is_unsupported() {
        let length = BigInt::from(1_u8) << usize::BITS;

        assert_eq!(
            make(&[int_term(length), item("x")]),
            Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::ResultTooLarge {
                    detail: format!(
                        "a List result of length a 65-bit integer needs more than \
                         {MAX_LIST_RESULT_LEN} elements"
                    ),
                }
            ))
        );
    }

    /// On a 32-bit target a `makeList` result is at most 512 MiB of 4-byte references, 2^27
    /// elements (see `bytes_lengths_are_bounded_by_what_the_target_can_allocate`); on a 64-bit
    /// target the floor binds first.
    #[test]
    fn make_length_is_bounded_by_what_the_target_can_allocate() {
        let thirty_two = target_result_bytes(u64::from(i32::MAX.unsigned_abs()));
        assert_eq!(list_length_limit(thirty_two, 4), 1 << 27);
        let sixty_four = target_result_bytes(i64::MAX.unsigned_abs());
        assert_eq!(list_length_limit(sixty_four, 8), MAX_LIST_RESULT_LEN);
    }

    /// `makeList` is refused above [`MAX_LIST_RESULT_LEN`] before anything is allocated: a
    /// length beyond the machine's memory aborted the process. Below it a length is built,
    /// however long: 2^25 elements, about 0.3 GB and a second to build, and the floor itself, 4 GiB
    /// of references (decided without allocating them here).
    #[test]
    fn make_length_is_bounded_before_allocating() {
        for length in [1_u64 << 25, MAX_LIST_RESULT_LEN] {
            assert_eq!(
                bounded_list_length(&BigInt::from(length)),
                Ok(usize::try_from(length).unwrap()),
                "makeList({length}, x)"
            );
        }
        assert!(bounded_list_length(&BigInt::from(MAX_LIST_RESULT_LEN + 1)).is_err());
        for length in [
            BigInt::from(MAX_LIST_RESULT_LEN + 1),
            BigInt::from(1_u64 << 40),
        ] {
            assert!(
                matches!(
                    make(&[int_term(length.clone()), item("x")]),
                    Ok(BuiltinResult::Unsupported(
                        UnsupportedHookReason::ResultTooLarge { .. }
                    ))
                ),
                "makeList({length}, x)"
            );
        }
        assert!(matches!(
            make(&[integer(3), item("x")]),
            Ok(BuiltinResult::Value(list)) if matches!(
                list.kind(),
                TermKind::List { heads, rest: None, .. } if heads.len() == 3
            )
        ));
    }

    #[test]
    fn indices_above_usize_are_out_of_range_for_concrete_lists() {
        let definition = definition();
        let list = Term::list(definition.clone(), vec![item("a"), item("b")], None);
        let replacement = Term::list(definition, vec![item("x")], None);
        let index = int_term(BigInt::from(1_u8) << usize::BITS);

        assert_eq!(
            get(&[list.clone(), index.clone()]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            range(&[list.clone(), index.clone(), integer(0)]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            update(&[list.clone(), index.clone(), item("x")]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            update_all(&[list, index, replacement]),
            Ok(BuiltinResult::Bottom)
        );
    }
}
