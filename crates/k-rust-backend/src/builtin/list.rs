//! Concrete `LIST` hooks: per-call operations on the internal list
//! representation; a responsibility, not an algorithm; no counter of its own, no worklist.
//!
//! Each hook is a few operations of the persistent positional tree that holds the list's items
//! (card `backend.term.chunked`), so for a list argument of `n` items:
//!
//! - `size`: `O(1)`, the root summary's count; `element`, `unit`: `O(1)`.
//! - `get`: one descent by position, `O(log n)` where a vector read in `O(1)`; measured on a
//!   rewrite loop reading every item of lists of 2,000 to 16,000 items, a read costs about the
//!   same (177 K instructions, the rewrite step) with either, so the descent is not visible.
//! - `concat`: one join, `O(log n)` for `n` the longer operand's items.
//! - `update`: one path copy, `O(log n)`; `range`: two splits, `O(log n)`; `updateAll`: two
//!   splits and two joins, `O(log n)` for `n` the longer operand's items.
//! - `make`: a bulk load of the `n` copies, `O(n)`; `in`: a scan, `O(n)` (no summary orders the
//!   items of a list by value).

use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

use k_rust_kore::names::BuiltinSort;

use super::{
    BuiltinResult, HookResult, ResultCollection, UnsupportedHookReason, bool_term,
    collection_item::{self, Operand},
    describe_int, expect_arity, expect_sort, int_term, read_int, values_differ,
};
use crate::{
    matching::SortGraph,
    term::{Items, Sort, Term, TermKind},
};

pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    sorts: Option<&SortGraph>,
    result: ResultCollection<'_>,
) -> HookResult<BuiltinResult> {
    let result = match hook {
        "LIST.concat" => concat(arguments, result),
        "LIST.element" => element(arguments, result),
        "LIST.in" => contains(arguments, sorts),
        "LIST.size" => size(arguments),
        "LIST.unit" => unit(arguments, result),
        "LIST.get" => return get(arguments),
        "LIST.make" => return make(arguments, result),
        "LIST.range" => return range(arguments, result),
        "LIST.update" => return update(arguments, result),
        "LIST.updateAll" => return update_all(arguments, result),
        _ => {
            return Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::NotImplemented,
            ));
        }
    }?;
    Ok(result.into())
}

/// `L1 L2`: the operands' trees joined where they meet (the left's heads, or its tails, before
/// the right's heads), `O(log n)` nodes built for operands of up to `n` items, whatever their
/// lengths; an opaque middle of either keeps its place.
fn concat(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("LIST.concat", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    let built = match (left.kind(), right.kind()) {
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
            let Some(into) = result.list(Some(left_definition)) else {
                return Ok(None);
            };
            let from = &left_definition.element_sort;
            let items = |terms: &Items<Term>| into.items(terms, from);
            let (Some(left_heads), Some(right_heads)) = (items(left_heads), items(right_heads))
            else {
                return Ok(None);
            };
            let (heads, rest) = match (left_rest, right_rest) {
                (None, _) => {
                    let rest = match right_rest {
                        Some((middle, tails)) => {
                            let Some(tails) = items(tails) else {
                                return Ok(None);
                            };
                            Some((middle.clone(), tails))
                        }
                        None => None,
                    };
                    (left_heads.join(&right_heads), rest)
                }
                (Some((middle, tails)), None) => {
                    let Some(tails) = items(tails) else {
                        return Ok(None);
                    };
                    (left_heads, Some((middle.clone(), tails.join(&right_heads))))
                }
                (Some(_), Some(_)) => return Ok(None),
            };
            into.build_items(heads, rest)
        }
        (
            TermKind::List {
                definition,
                heads,
                rest: None,
            },
            _,
        ) => {
            let Some(into) = result.list(Some(definition)) else {
                return Ok(None);
            };
            let Some(heads) = into.items(heads, &definition.element_sort) else {
                return Ok(None);
            };
            into.build_items(heads, Some((right.clone(), Items::new())))
        }
        (
            _,
            TermKind::List {
                definition,
                heads,
                rest: None,
            },
        ) => {
            let Some(into) = result.list(Some(definition)) else {
                return Ok(None);
            };
            let Some(heads) = into.items(heads, &definition.element_sort) else {
                return Ok(None);
            };
            into.build_items(Items::new(), Some((left.clone(), heads)))
        }
        _ => None,
    };
    Ok(built)
}

fn element(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("LIST.element", arguments, 1)?;
    let Some(into) = result.list(None) else {
        return Ok(None);
    };
    let Some(element) = into.element(arguments[0].clone()) else {
        return Ok(None);
    };
    Ok(into.build(vec![element], None))
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

/// `E in L`: `true` when `E` is syntactically one of `L`'s known elements, which every instance
/// of `L` holds (the heads and, of an open list, the tails around its opaque middle); `false` only
/// for a closed list whose every element is apart from `E`, since an open list's middle may hold
/// any element; unevaluated otherwise. `E` is read as an element of `L`'s element sort
/// (`collection_item`).
fn contains(arguments: &[Term], sorts: Option<&SortGraph>) -> HookResult<Option<Term>> {
    expect_arity("LIST.in", arguments, 2)?;
    let [element, list] = arguments else {
        unreachable!()
    };
    let TermKind::List {
        definition,
        heads,
        rest,
    } = list.kind()
    else {
        return Ok(None);
    };
    let element = match collection_item::read(sorts, element, &definition.element_sort) {
        Operand::Element(element) => element,
        Operand::Wider { item, sort } => {
            return Ok((rest.is_none()
                && collection_item::absent_above(
                    sorts,
                    item,
                    &sort,
                    &definition.element_sort,
                    heads.iter(),
                ))
            .then(|| bool_term(false)));
        }
        Operand::Unrelated => return Ok(None),
    };
    let tails = rest.as_ref().map(|(_, tails)| tails.iter());
    if heads
        .iter()
        .chain(tails.into_iter().flatten())
        .any(|item| *item == *element)
    {
        return Ok(Some(bool_term(true)));
    }
    Ok((rest.is_none()
        && heads
            .iter()
            .all(|head| values_differ(sorts, &element, head)))
    .then(|| bool_term(false)))
}

/// `makeList(N, V)`: `N` copies of `V`, built in `O(log² N)` nodes ([`Items::repeat`]): one node
/// stands for every subtree of the copies that holds the same items in the same shape, so the
/// application holds memory logarithmic in `N`, not proportional to it, and every length the
/// list's tree counts is computed ([`bounded_list_length`]).
fn make(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<BuiltinResult> {
    expect_arity("LIST.make", arguments, 2)?;
    let [length, value] = arguments else {
        unreachable!()
    };
    let Some(length) = read_int(length) else {
        expect_sort("LIST.make", length, &Sort::builtin(BuiltinSort::Int))?;
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(into) = result.list(None) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(value) = into.element(value.clone()) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if length.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let concrete_length = match bounded_list_length(&length) {
        Ok(length) => length,
        Err(reason) => return Ok(BuiltinResult::Unsupported(reason)),
    };
    Ok(into
        .build_items(Items::repeat(&value, concrete_length), None)
        .into())
}

/// A nonnegative `makeList` length as a number of elements, or `ResultTooLarge` when the list's
/// tree cannot count it: a tree counts its items in a `usize`, so a longer list exists and the
/// backend does not build it.
fn bounded_list_length(length: &BigInt) -> Result<usize, UnsupportedHookReason> {
    debug_assert!(
        length.sign() != Sign::Minus,
        "makeList of a negative length is undefined, checked by the caller"
    );
    length
        .to_usize()
        .ok_or_else(|| UnsupportedHookReason::ResultTooLarge {
            detail: format!(
                "a List result of length {} is longer than the {} items a list counts on this \
                 target",
                describe_int(length),
                usize::MAX,
            ),
        })
}

/// `range(L, front, back)`: `L` without its first `front` and last `back` items, cut from its
/// trees at those positions, `O(log n)` nodes; of an open list, the cuts fall in its heads and
/// its tails, which must be long enough to hold them.
fn range(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<BuiltinResult> {
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
    let Some(into) = result.list(Some(definition)) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if front.sign() == Sign::Minus || back.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let front = front.to_usize();
    let back = back.to_usize();
    let from = &definition.element_sort;
    let range = match rest {
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
            let (range, _) = heads.split_at(front).1.split_at(end - front);
            into.items(&range, from)
                .and_then(|range| into.build_items(range, None))
        }
        Some((middle, tails)) => {
            let (Some(front), Some(back)) = (front, back) else {
                return Ok(BuiltinResult::NotApplicable);
            };
            if front > heads.len() || back > tails.len() {
                return Ok(BuiltinResult::NotApplicable);
            };
            let (_, heads) = heads.split_at(front);
            let (tails, _) = tails.split_at(tails.len() - back);
            match (into.items(&heads, from), into.items(&tails, from)) {
                (Some(heads), Some(tails)) => {
                    into.build_items(heads, Some((middle.clone(), tails)))
                }
                _ => None,
            }
        }
    };
    Ok(range.into())
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

fn unit(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("LIST.unit", arguments, 0)?;
    Ok(result
        .list(None)
        .and_then(|into| into.build(Vec::new(), None)))
}

/// `L[index <- value]`: the heads' tree with the one item replaced where it stands, the path to
/// it copied, `O(log n)` nodes.
fn update(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<BuiltinResult> {
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
    let Some(into) = result.list(Some(definition)) else {
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
    let from = &definition.element_sort;
    let rest = match rest {
        Some((middle, tails)) => match into.items(tails, from) {
            Some(tails) => Some((middle.clone(), tails)),
            None => return Ok(BuiltinResult::NotApplicable),
        },
        None => None,
    };
    let (Some(heads), Some(value)) = (into.items(heads, from), into.element(value.clone())) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(into
        .build_items(heads.replace_at(index, value), rest)
        .into())
}

/// `updateList(dest, index, src)`: `dest` cut before `index` and after the `m` items `src`
/// replaces, and the three trees joined, `O(log n)` nodes whatever `m` is: `src`'s tree is
/// shared, not copied.
fn update_all(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<BuiltinResult> {
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
    let Some(into) = result.list(Some(definition)) else {
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
    let from = &definition.element_sort;
    let (Some(original), Some(updates)) = (into.items(original, from), into.items(updates, from))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let (before, replaced) = original.split_at(index);
    let (_, after) = replaced.split_at(end - index);
    Ok(into
        .build_items(before.join(&updates).join(&after), None)
        .into())
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::term::{CollectionMetadata, CollectionSymbols, ListDefinition, Variable};

    fn definition() -> Arc<ListDefinition> {
        Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: "unit".into(),
                element: "element".into(),
                concat: "concat".into(),
            },
            element_sort: Sort::simple("SortItem"),
            list_sort: "SortItems".into(),
        })
    }

    fn items() -> CollectionMetadata {
        CollectionMetadata::List(definition())
    }

    fn into(collection: &CollectionMetadata) -> ResultCollection<'_> {
        ResultCollection::declared(Some(collection), None)
    }

    fn item(value: &str) -> Term {
        Term::raw_domain_value(Sort::simple("SortItem"), value)
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
            range(&[list, integer(1), integer(1)], into(&items())),
            Ok(BuiltinResult::Value(expected))
        );
    }

    /// Every instance of an open list holds its known elements, heads and tails alike, so an
    /// element syntactically equal to one is a member; none is ever known not to be one, since
    /// the opaque middle may hold any element.
    #[test]
    fn membership_in_an_open_list_holds_on_a_known_element_and_is_never_false() {
        let middle = Term::variable(Variable::new("REST", Sort::simple("SortItems")));
        let list = Term::list(
            definition(),
            vec![item("a")],
            Some((middle, vec![item("c")])),
        );

        assert_eq!(
            contains(&[item("a"), list.clone()], None),
            Ok(Some(bool_term(true)))
        );
        assert_eq!(
            contains(&[item("c"), list.clone()], None),
            Ok(Some(bool_term(true)))
        );
        assert_eq!(contains(&[item("b"), list], None), Ok(None));
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

    /// `makeList` builds its result in the list sort the applied symbol declares, and a symbol
    /// whose result sort is no list sort gets no value from it.
    #[test]
    fn make_builds_the_declared_result_list() {
        let BuiltinResult::Value(made) = make(&[integer(2), item("x")], into(&items())).unwrap()
        else {
            panic!("LIST.make should evaluate")
        };
        assert_eq!(
            made,
            Term::list(definition(), vec![item("x"), item("x")], None)
        );
        for result in [
            ResultCollection::declared(None, None),
            ResultCollection::undeclared(None),
        ] {
            assert_eq!(
                make(&[integer(2), item("x")], result),
                Ok(BuiltinResult::NotApplicable)
            );
        }
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

        assert_eq!(
            concat(&[left, right], into(&items())),
            Ok(Some(joined.clone()))
        );
        assert_eq!(
            update(&[joined.clone(), integer(1), item("x")], into(&items())),
            Ok(BuiltinResult::Value(changed))
        );
        assert_eq!(size(&[joined]), Ok(Some(integer(3))));
    }

    /// The LIST hooks that cut, join or replace a long list edit its trees: each computes the
    /// own summaries of at most the items of the leaves its edits copy, a leaf and a neighbour
    /// at each cut, junction or replaced position, not one per item of the list, and the result
    /// is the list of the items it should hold.
    #[test]
    fn hooks_that_cut_join_or_replace_a_long_list_summarize_only_the_leaves_they_edit() {
        const ITEMS: usize = 4096;
        let leaf = crate::term::chunked::DEFAULT_BRANCHING;
        let numbers = |values: &[usize]| -> Vec<Term> {
            values
                .iter()
                .map(|value| item(&value.to_string()))
                .collect()
        };
        let closed = |items: Vec<Term>| Term::list(definition(), items, None);
        let all = (0..ITEMS).collect::<Vec<_>>();
        let base = closed(numbers(&all));
        let middle = Term::variable(Variable::new("REST", Sort::simple("SortItems")));
        let open = Term::list(
            definition(),
            numbers(&all),
            Some((middle.clone(), numbers(&all))),
        );
        let edited = |at: usize, with: &[usize]| {
            let mut items = all.clone();
            items.splice(at..at + with.len(), with.iter().copied());
            numbers(&items)
        };
        let appended = numbers(&all.iter().copied().chain([ITEMS]).collect::<Vec<_>>());
        let prepended = numbers(
            &[ITEMS]
                .into_iter()
                .chain(all.iter().copied())
                .collect::<Vec<_>>(),
        );
        let cases: Vec<(&str, Vec<Term>, usize, Term)> = vec![
            (
                "LIST.concat",
                vec![base.clone(), closed(numbers(&[ITEMS]))],
                1,
                closed(appended),
            ),
            (
                "LIST.concat",
                vec![closed(numbers(&[ITEMS])), base.clone()],
                1,
                closed(prepended),
            ),
            (
                "LIST.concat",
                vec![base.clone(), base.clone()],
                1,
                closed(numbers(
                    &all.iter().chain(&all).copied().collect::<Vec<_>>(),
                )),
            ),
            (
                "LIST.range",
                vec![base.clone(), integer(1000), integer(1000)],
                2,
                closed(numbers(&all[1000..ITEMS - 1000])),
            ),
            (
                "LIST.range",
                vec![open.clone(), integer(1000), integer(1000)],
                2,
                Term::list(
                    definition(),
                    numbers(&all[1000..]),
                    Some((middle, numbers(&all[..ITEMS - 1000]))),
                ),
            ),
            (
                "LIST.update",
                vec![base.clone(), integer(2000), item("x")],
                1,
                {
                    let mut items = numbers(&all);
                    items[2000] = item("x");
                    closed(items)
                },
            ),
            (
                "LIST.updateAll",
                vec![base.clone(), integer(1000), closed(numbers(&[7, 8, 9]))],
                4,
                closed(edited(1000, &[7, 8, 9])),
            ),
            (
                "LIST.updateAll",
                vec![base.clone(), integer(1000), base_part(&base, 3000)],
                4,
                closed(edited(1000, &all[..3000])),
            ),
        ];
        for (name, arguments, edits, expected) in cases {
            let mut result = None;
            let summaries = crate::term::items::element_summaries_during(|| {
                result = Some(evaluate(name, &arguments, None, into(&items())));
            });
            let result = match result {
                Some(Ok(BuiltinResult::Value(result))) => result,
                other => panic!("{name}: {other:?}"),
            };
            assert_eq!(result, expected, "{name}");
            assert!(
                summaries <= edits * 2 * leaf,
                "{name}: {summaries} item summaries for {edits} edits of leaves of at most {leaf}"
            );
        }
    }

    /// The first `items` items of `list`, a closed list, as a list sharing its nodes.
    fn base_part(list: &Term, items: usize) -> Term {
        let TermKind::List {
            heads, rest: None, ..
        } = list.kind()
        else {
            panic!("a closed list: {list:?}");
        };
        Term::list_of_items(definition(), heads.split_at(items).0, None)
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

        assert_eq!(concat(&[left, right], into(&items())), Ok(None));
    }

    #[test]
    fn partial_list_hooks_return_bottom_for_undefined_inputs() {
        let definition = definition();
        let list = Term::list(definition.clone(), vec![item("a"), item("b")], None);
        let replacement = Term::list(definition, vec![item("x"), item("y")], None);

        assert_eq!(get(&[list.clone(), integer(2)]), Ok(BuiltinResult::Bottom));
        assert_eq!(
            update(&[list.clone(), integer(-1), item("x")], into(&items())),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            update_all(&[list.clone(), integer(1), replacement], into(&items())),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            range(&[list, integer(2), integer(1)], into(&items())),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            make(&[integer(-1), item("x")], into(&items())),
            Ok(BuiltinResult::Bottom)
        );
    }

    /// A length the list's tree cannot count is refused, and the refusal names the length and
    /// the count.
    #[test]
    fn make_length_above_usize_is_unsupported() {
        let length = BigInt::from(1_u8) << usize::BITS;
        assert_eq!(
            make(&[int_term(length), item("x")], into(&items())),
            Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::ResultTooLarge {
                    detail: format!(
                        "a List result of length a {}-bit integer is longer than the {} items a \
                         list counts on this target",
                        usize::BITS + 1,
                        usize::MAX,
                    ),
                }
            ))
        );
    }

    /// Every length a list counts is computed, up to `usize::MAX`, and the result holds that
    /// many copies of the value: its length, its items at both ends, and an edit at a position
    /// far inside it.
    #[test]
    fn make_computes_every_length_a_list_counts() {
        for length in [0, 3, 1 << 40, usize::MAX] {
            let Ok(BuiltinResult::Value(list)) =
                make(&[int_term(length.into()), item("x")], into(&items()))
            else {
                panic!("makeList({length}, x) is computed");
            };
            let TermKind::List {
                heads, rest: None, ..
            } = list.kind()
            else {
                panic!("makeList({length}, x) is a closed list");
            };
            assert_eq!(heads.len(), length);
            if length > 0 {
                assert_eq!(heads.first(), Some(&item("x")));
                assert_eq!(heads.last(), Some(&item("x")));
                let edited = heads.replace_at(length / 2, item("y"));
                assert_eq!(edited.get(length / 2), Some(&item("y")));
                assert_eq!(
                    edited.get(length / 2 - usize::from(length > 1)),
                    Some(&item("x"))
                );
            }
        }
    }

    /// One `makeList` application holds memory that grows with the levels of its tree, not with
    /// its length: measured with the test allocator between `2^12` and `2^24` copies, the peak
    /// grows by less than one handle per leaf the copies would fill if each leaf were its own
    /// node (a tree of one reference per copy grows by at least `B` times that). The tree of
    /// `2^24` copies has three more levels, each a few nodes of at most `B` handles: 5,312 bytes
    /// measured, against 4 MiB for the bound and 128 MiB for one reference per copy.
    #[test]
    fn make_holds_memory_logarithmic_in_its_length() {
        let metadata = items();
        let peak = |length: u64| {
            let arguments = [int_term(length.into()), item("x")];
            let (result, peak) =
                crate::peak_memory::peak_during(|| make(&arguments, into(&metadata)));
            assert!(matches!(result, Ok(BuiltinResult::Value(_))));
            peak
        };
        let (shorter, longer) = (1_u64 << 12, 1_u64 << 24);
        let growth = peak(longer).saturating_sub(peak(shorter));
        let references = (longer - shorter) * size_of::<Term>() as u64;
        let branching = crate::term::chunked::DEFAULT_BRANCHING as u64;
        assert!(
            growth < references / branching,
            "the peak grew by {growth} bytes over {references} bytes of references"
        );
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
            range(&[list.clone(), index.clone(), integer(0)], into(&items())),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            update(&[list.clone(), index.clone(), item("x")], into(&items())),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            update_all(&[list, index, replacement], into(&items())),
            Ok(BuiltinResult::Bottom)
        );
    }
}
