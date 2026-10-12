//! Deterministic `SET` hooks: per-call operations on the internal set representation; a
//! responsibility, not an algorithm; no counter of its own, no worklist.

use std::sync::Arc;

use num_bigint::BigInt;

use super::{
    BuiltinResult, HookResult, ResultCollection, UnsupportedHookReason, bool_term, expect_arity,
    int_term, values_differ,
};
use crate::{
    matching::SortGraph,
    term::{Items, SetDefinition, Term, TermKind},
};

pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    sorts: Option<&SortGraph>,
    result: ResultCollection<'_>,
) -> HookResult<BuiltinResult> {
    // A hooked application is strict in its arguments, and an internal set that holds an
    // element twice is `\bottom`: set concatenation is nilpotent (`Term::set`). A `ceil_free`
    // set has pairwise distinct elements, so only other sets are asked, and their elements'
    // summary says whether two adjacent ones are equal (`Term::repeated_set_element`).
    if arguments.iter().any(|argument| {
        !argument.attributes().ceil_free() && argument.repeated_set_element().is_some()
    }) {
        return Ok(BuiltinResult::Bottom);
    }
    let result = match hook {
        "SET.concat" => return concat(arguments, result),
        "SET.element" => element(arguments, result),
        "SET.unit" => unit(arguments, result),
        "SET.in" => contains(arguments, sorts),
        "SET.difference" => difference(arguments, result),
        "SET.set2list" => to_list(arguments, result),
        "SET.size" => size(arguments),
        "SET.intersection" => intersection(arguments, result),
        "SET.union" => union(arguments, result),
        "SET.list2set" => list_to_set(arguments, result),
        "SET.inclusion" => inclusion(arguments),
        _ => {
            return Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::NotImplemented,
            ));
        }
    }?;
    Ok(result.into())
}

/// `S1 S2`, the disjoint union: `\bottom` when the operands share an element, because set
/// concatenation is nilpotent (`SetItem(X) SetItem(X)` is `\bottom`; the union is `|Set`).
/// Syntactically equal elements are equal values, so a shared one decides the overlap on every
/// instance. Elements that are not syntactically equal stay apart in the result, and the
/// result's definedness (`ceil_term`) carries the condition that they differ.
fn concat(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<BuiltinResult> {
    expect_arity("SET.concat", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    let (
        TermKind::Set {
            definition: left_definition,
            elements: left_elements,
            rest: left_rest,
        },
        TermKind::Set {
            definition: right_definition,
            elements: right_elements,
            rest: right_rest,
        },
    ) = (left.kind(), right.kind())
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if left_definition != right_definition || (left_rest.is_some() && right_rest.is_some()) {
        return Ok(BuiltinResult::NotApplicable);
    }
    let Some(into) = result.set(Some(left_definition)) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    // An element both operands hold makes the concatenation `\bottom`. Each operand holds an
    // element once (`evaluate`) and holds its elements ordered, so in the ordered union of the
    // two the occurrences of an element both hold stand side by side, which the union's summary
    // records (`collision`): the check costs the union, `O(m log(n/m + 1))` nodes for operands
    // of `n` and `m` elements, rather than a pass over both.
    let united = left_elements.union(right_elements);
    if united.summary().collision {
        return Ok(BuiltinResult::Bottom);
    }
    Ok(into
        .build_from(
            united,
            &left_definition.element_sort,
            left_rest.clone().or_else(|| right_rest.clone()),
        )
        .into())
}

fn element(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("SET.element", arguments, 1)?;
    let Some(into) = result.set(None) else {
        return Ok(None);
    };
    let Some(element) = into.element(arguments[0].clone()) else {
        return Ok(None);
    };
    Ok(into.build(vec![element], None))
}

fn unit(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("SET.unit", arguments, 0)?;
    Ok(result
        .set(None)
        .and_then(|into| into.build(Vec::new(), None)))
}

fn contains(arguments: &[Term], sorts: Option<&SortGraph>) -> HookResult<Option<Term>> {
    expect_arity("SET.in", arguments, 2)?;
    let [element, set] = arguments else {
        unreachable!()
    };
    let TermKind::Set { elements, rest, .. } = set.kind() else {
        return Ok(None);
    };
    if place_of(elements, element).is_ok() {
        Ok(Some(bool_term(true)))
    } else if absent(sorts, element, elements, rest) {
        Ok(Some(bool_term(false)))
    } else {
        Ok(None)
    }
}

/// The place of `element` among `elements`, syntactically: `Ok` with the index of an element
/// that is the same term, or `Err` with the index at which it would go.
///
/// `elements` are the elements of a set argument as `Term::set` stores them, in the order of
/// `Term`, under which two terms compare equal exactly when they are the same term, so a binary
/// search decides whether `element` is among them in `O(log n)` comparisons.
fn place_of(elements: &Items<Term>, element: &Term) -> Result<usize, usize> {
    elements.search_by(|existing| {
        #[cfg(test)]
        compared_with_an_element();
        existing.cmp(element)
    })
}

#[cfg(test)]
thread_local! {
    /// Test builds: the elements of a set this thread's `SET.in` has compared an element with,
    /// by the search (`place_of`) or element by element (`absent`).
    static ELEMENT_COMPARISONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn compared_with_an_element() {
    ELEMENT_COMPARISONS.with(|count| count.set(count.get() + 1));
}

/// Whether `element`, which is none of `elements` syntactically, is a value the set does not
/// hold.
///
/// Without a rest, the set holds its elements and nothing else. Strict operands make apartness
/// a difference of values, so an element different from each of the set's is absent. Two
/// constructor-like terms denote different values exactly when they differ syntactically, so a
/// constructor-like `element` differs from every constructor-like element of the set already,
/// and is compared only with the elements that are not constructor-like: the elements' summary
/// counts them and leads to them (`Items::symbolic_keyed`), `O(s log n)` nodes for `s` such
/// elements among `n`. An element that is not constructor-like is compared with each element.
fn absent(
    sorts: Option<&SortGraph>,
    element: &Term,
    elements: &Items<Term>,
    rest: &Option<Term>,
) -> bool {
    let differs = |existing: &Term| {
        #[cfg(test)]
        compared_with_an_element();
        values_differ(sorts, element, existing)
    };
    rest.is_none()
        && if element.attributes().constructor_like {
            elements.symbolic_keyed().all(differs)
        } else {
            elements.iter().all(differs)
        }
}

/// `S1 -Set S2`, the elements of `S1` that are none of `S2`'s, of two closed sets of
/// constructor-like elements (`concrete_set`), for which being none of them syntactically is
/// being a different value.
///
/// Both operands are ordered trees. When `S2` is the smaller, each of its `m` elements is
/// searched in `S1` and removed from it where found, a path copy each, so the result shares the
/// rest of `S1`'s tree: `O(m log n)`. Otherwise the elements of `S1` are each searched in `S2`
/// and those not found are loaded into a new tree, `O(n log m)` for the `n <= m` elements of
/// `S1`.
fn difference(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("SET.difference", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    let Some((definition, left_elements)) = concrete_set(left) else {
        return Ok(None);
    };
    let Some((right_definition, right_elements)) = concrete_set(right) else {
        return Ok(None);
    };
    if definition != right_definition {
        return Ok(None);
    }
    let Some(into) = result.set(Some(definition)) else {
        return Ok(None);
    };
    let kept = if right_elements.len() < left_elements.len() {
        right_elements
            .iter()
            .fold(left_elements.clone(), |kept, element| {
                match kept.search(element) {
                    Ok(index) => kept.remove_at(index).0,
                    Err(_) => kept,
                }
            })
    } else {
        Items::tree(
            left_elements
                .iter()
                .filter(|element| right_elements.search(element).is_err())
                .cloned()
                .collect(),
        )
    };
    Ok(into.build_from(kept, &definition.element_sort, None))
}

fn to_list(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("SET.set2list", arguments, 1)?;
    let Some((definition, elements)) = concrete_set(&arguments[0]) else {
        return Ok(None);
    };
    let Some(into) = result.list(None) else {
        return Ok(None);
    };
    Ok(into
        .elements(elements, &definition.element_sort)
        .and_then(|elements| into.build(elements, None)))
}

fn size(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("SET.size", arguments, 1)?;
    let Some((_, elements)) = concrete_set(&arguments[0]) else {
        return Ok(None);
    };
    Ok(Some(int_term(BigInt::from(elements.len()))))
}

/// `S1 /\Set S2` (`SET.intersection`), the elements both closed sets of constructor-like
/// elements hold, for which being the same term is being the same value: each element of the
/// smaller operand is searched in the larger, `O(m log n)` for operands of `m <= n` elements, and
/// those found, in order, are loaded into a new tree.
fn intersection(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("SET.intersection", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    let Some((definition, left_elements)) = concrete_set(left) else {
        return Ok(None);
    };
    let Some((right_definition, right_elements)) = concrete_set(right) else {
        return Ok(None);
    };
    if definition != right_definition {
        return Ok(None);
    }
    let Some(into) = result.set(Some(definition)) else {
        return Ok(None);
    };
    let (smaller, larger) = smaller_first(left_elements, right_elements);
    let common = smaller
        .iter()
        .filter(|element| larger.search(element).is_ok())
        .cloned()
        .collect();
    Ok(into.build_from(Items::tree(common), &definition.element_sort, None))
}

/// The two operands, the one with fewer elements first (the left one when they hold as many).
fn smaller_first<'a>(
    left: &'a Items<Term>,
    right: &'a Items<Term>,
) -> (&'a Items<Term>, &'a Items<Term>) {
    if right.len() < left.len() {
        (right, left)
    } else {
        (left, right)
    }
}

/// `S1 |Set S2`, the set of the elements of either set.
///
/// A value of the union holds each value of either operand once, so it is the set of the left
/// operand's elements and of the right operand's elements that are none of the left's. That set
/// is determined only when each element of one operand is known to be equal to, or different
/// from, each element of the other. Constructor-like elements are both: two of them denote the
/// same value exactly when they are the same term. So two closed sets of constructor-like
/// elements (`concrete_set`) have a union: the larger operand with the smaller's elements it
/// lacks, a common element kept once. Any other operands give no result: an element that may or
/// may not equal one of the other operand's makes the union's size undecided, and a set with
/// a rest holds elements the hook cannot see.
fn union(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("SET.union", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    let Some((definition, left_elements)) = concrete_set(left) else {
        return Ok(None);
    };
    let Some((right_definition, right_elements)) = concrete_set(right) else {
        return Ok(None);
    };
    if definition != right_definition {
        return Ok(None);
    }
    let Some(into) = result.set(Some(definition)) else {
        return Ok(None);
    };
    // The elements of the smaller operand that the larger lacks, each found missing by a search,
    // united with the larger operand's tree: `O(m log n)` for operands of `m <= n` elements, and
    // the result shares the larger tree's nodes that receive none of them.
    let (smaller, larger) = smaller_first(left_elements, right_elements);
    let missing = smaller
        .iter()
        .filter(|element| larger.search(element).is_err())
        .cloned()
        .collect();
    Ok(into.build_from(
        larger.union(&Items::tree(missing)),
        &definition.element_sort,
        None,
    ))
}

fn list_to_set(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("SET.list2set", arguments, 1)?;
    let TermKind::List {
        definition,
        heads,
        rest: None,
    } = arguments[0].kind()
    else {
        return Ok(None);
    };
    if heads
        .iter()
        .any(|element| !element.attributes().constructor_like)
    {
        return Ok(None);
    }
    let Some(into) = result.set(None) else {
        return Ok(None);
    };
    // The set of the list's elements: a list may repeat one, and the set holds it once. This
    // is not a concatenation, so the repeat is removed here (`Term::set` keeps repeats).
    let Some(mut elements) = into.elements(heads, &definition.element_sort) else {
        return Ok(None);
    };
    elements.sort();
    elements.dedup();
    Ok(into.build(elements, None))
}

fn inclusion(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("SET.inclusion", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    let Some((left_definition, left_elements)) = concrete_set(left) else {
        return Ok(None);
    };
    let Some((right_definition, right_elements)) = concrete_set(right) else {
        return Ok(None);
    };
    if left_definition != right_definition {
        return Ok(None);
    }
    Ok(Some(bool_term(
        left_elements
            .iter()
            .all(|element| right_elements.search(element).is_ok()),
    )))
}

/// The definition and the elements of `term` when it is a set without a rest whose elements are
/// all constructor-like, which the elements' summary counts (`Items::symbolic_keys`).
fn concrete_set(term: &Term) -> Option<(&Arc<SetDefinition>, &Items<Term>)> {
    let TermKind::Set {
        definition,
        elements,
        rest: None,
    } = term.kind()
    else {
        return None;
    };
    (elements.symbolic_keys() == 0).then_some((definition, elements))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};

    use crate::term::{CollectionMetadata, CollectionSymbols, ListDefinition, Sort, Variable};

    fn shape(name: &str) -> Arc<ListDefinition> {
        Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: format!("{name}-unit").into(),
                element: format!("{name}-element").into(),
                concat: format!("{name}-concat").into(),
            },
            element_sort: Sort::simple("SortKItem"),
            list_sort: name.into(),
        })
    }

    fn set_definition() -> Arc<SetDefinition> {
        shape("SortSet")
    }

    fn list_definition() -> Arc<ListDefinition> {
        shape("SortList")
    }

    fn sets() -> CollectionMetadata {
        CollectionMetadata::Set(set_definition())
    }

    fn lists() -> CollectionMetadata {
        CollectionMetadata::List(list_definition())
    }

    fn into(collection: &CollectionMetadata) -> ResultCollection<'_> {
        ResultCollection::declared(Some(collection), None)
    }

    fn item(value: &str) -> Term {
        Term::domain_value(Sort::simple("SortKItem"), value)
    }

    fn set(values: &[&str]) -> Term {
        Term::set(
            set_definition(),
            values.iter().map(|value| item(value)).collect(),
            None,
        )
    }

    #[test]
    fn fu17_set_membership_separates_symbolic_elements() {
        let int = Sort::simple("SortInt");
        let element_sort = Sort::simple("SortKItem");
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
        let collection = Term::set(set_definition(), vec![a.clone()], None);
        assert_eq!(
            super::super::evaluate_hook("SET.in", &[b.clone(), collection.clone()])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(bool_term(false))
        );
        assert_eq!(
            super::super::evaluate_hook("SET.in", &[a.clone(), collection.clone()])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(bool_term(true))
        );
        let open = Term::set(
            set_definition(),
            vec![a.clone()],
            Some(Term::variable(Variable::new(
                "REST",
                Sort::simple("SortSet"),
            ))),
        );
        assert_eq!(
            super::super::evaluate_hook("SET.in", &[b, open.clone()])
                .unwrap()
                .unwrap(),
            BuiltinResult::NotApplicable,
        );
        assert_eq!(
            super::super::evaluate_hook("SET.in", &[a, open])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(bool_term(true)),
        );
        let variable = Term::variable(Variable::new("C", element_sort));
        assert_eq!(
            super::super::evaluate_hook("SET.in", &[variable, collection])
                .unwrap()
                .unwrap(),
            BuiltinResult::NotApplicable
        );
    }

    #[test]
    fn concrete_set_algebra_matches_kore() {
        let left = set(&["a", "b"]);
        let right = set(&["b", "c"]);

        assert_eq!(
            difference(&[left.clone(), right.clone()], into(&sets())),
            Ok(Some(set(&["a"])))
        );
        assert_eq!(
            intersection(&[left.clone(), right.clone()], into(&sets())),
            Ok(Some(set(&["b"])))
        );
        assert_eq!(
            inclusion(&[set(&["a"]), left.clone()]),
            Ok(Some(bool_term(true)))
        );
        assert_eq!(inclusion(&[right, left]), Ok(Some(bool_term(false))));
    }

    #[test]
    fn membership_and_size_require_concrete_sets() {
        let concrete = set(&["a", "b"]);
        let symbolic = Term::set(
            set_definition(),
            vec![Term::variable(Variable::new(
                "X",
                Sort::simple("SortKItem"),
            ))],
            None,
        );

        assert_eq!(
            contains(&[item("a"), concrete.clone()], None),
            Ok(Some(bool_term(true)))
        );
        assert_eq!(
            contains(&[item("c"), concrete.clone()], None),
            Ok(Some(bool_term(false)))
        );
        assert_eq!(
            size(std::slice::from_ref(&concrete)),
            Ok(Some(int_term(BigInt::from(2))))
        );
        assert_eq!(contains(&[item("a"), symbolic], None), Ok(None));
    }

    #[test]
    fn list_and_set_conversions_are_deterministic() {
        let list = Term::list(
            list_definition(),
            vec![item("b"), item("a"), item("b")],
            None,
        );
        let expected_set = set(&["a", "b"]);

        assert_eq!(
            list_to_set(&[list], into(&sets())),
            Ok(Some(expected_set.clone()))
        );
        assert_eq!(
            to_list(&[expected_set], into(&lists())),
            Ok(Some(Term::list(
                list_definition(),
                vec![item("a"), item("b")],
                None,
            )))
        );
    }

    #[test]
    fn concat_preserves_one_opaque_remainder() {
        let rest = Term::variable(Variable::new("REST", Sort::simple("SortSet")));
        let left = Term::set(set_definition(), vec![item("a")], Some(rest.clone()));
        let right = set(&["b"]);

        assert_eq!(
            concat(&[left, right], into(&sets())),
            Ok(BuiltinResult::Value(Term::set(
                set_definition(),
                vec![item("a"), item("b")],
                Some(rest)
            )))
        );
    }

    #[test]
    fn concat_of_sets_sharing_an_element_is_bottom() {
        assert_eq!(
            concat(&[set(&["a", "b"]), set(&["b", "c"])], into(&sets())),
            Ok(BuiltinResult::Bottom)
        );
        let rest = Term::variable(Variable::new("REST", Sort::simple("SortSet")));
        let left = Term::set(set_definition(), vec![item("a")], Some(rest));
        assert_eq!(
            concat(&[left, set(&["a"])], into(&sets())),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            concat(&[set(&["a"]), set(&["b"])], into(&sets())),
            Ok(BuiltinResult::Value(set(&["a", "b"])))
        );
    }

    #[test]
    fn a_set_argument_holding_an_element_twice_makes_the_hook_bottom() {
        let repeated = Term::set(set_definition(), vec![item("a"), item("a")], None);
        assert_eq!(repeated.repeated_set_element(), Some(&item("a")));
        for (hook, arguments) in [
            ("SET.size", vec![repeated.clone()]),
            ("SET.in", vec![item("a"), repeated.clone()]),
            ("SET.difference", vec![repeated.clone(), set(&["b"])]),
            ("SET.set2list", vec![repeated]),
        ] {
            assert_eq!(
                evaluate(hook, &arguments, None, into(&lists())),
                Ok(BuiltinResult::Bottom),
                "{hook}"
            );
        }
    }

    /// `SET.in` decided by comparing the element with each element of the set: syntactic
    /// membership, else absence when there is no rest and the element is apart from each.
    fn membership_by_scan(element: &Term, set: &Term) -> Option<bool> {
        let TermKind::Set { elements, rest, .. } = set.kind() else {
            return None;
        };
        if elements.iter().any(|existing| existing == element) {
            Some(true)
        } else if rest.is_none()
            && elements
                .iter()
                .all(|existing| values_differ(None, element, existing))
        {
            Some(false)
        } else {
            None
        }
    }

    fn membership(element: &Term, set: &Term) -> Option<bool> {
        contains(&[element.clone(), set.clone()], None)
            .unwrap()
            .map(|answer| answer == bool_term(true))
    }

    /// Sets of every size up to 33 hold the even numbers below twice their size; membership of
    /// every number up to one past the last is what the set says. The elements' text order
    /// (`"10"` before `"2"`) is not their numeric order, and the search follows the terms'
    /// order, not the numbers'.
    #[test]
    fn membership_answers_the_elements_at_every_place_in_sets_of_every_size() {
        for size in 0..=33_u32 {
            let held = (0..size).map(|index| 2 * index).collect::<BTreeSet<_>>();
            let texts = held.iter().map(u32::to_string).collect::<Vec<_>>();
            let collection = set(&texts.iter().map(String::as_str).collect::<Vec<_>>());
            assert!(collection.attributes().constructor_like);
            for probe in 0..=2 * size + 1 {
                let probed = item(&probe.to_string());
                assert_eq!(
                    super::super::evaluate_hook("SET.in", &[probed.clone(), collection.clone()])
                        .unwrap()
                        .unwrap(),
                    BuiltinResult::Value(bool_term(held.contains(&probe))),
                    "size {size}, element {probe}"
                );
                assert_eq!(
                    membership(&probed, &collection),
                    membership_by_scan(&probed, &collection),
                    "size {size}, element {probe}"
                );
            }
        }
    }

    /// Every set drawn from ground elements, a variable and symbolic constructor applications,
    /// closed or with a rest, answers membership of each of those elements and of others exactly
    /// as comparing with each element does: present, absent, and undecided alike. The shortcut
    /// applies only to constructor-like elements of constructor-like sets; a symbolic element
    /// either way leaves the comparison with each element to decide.
    #[test]
    fn membership_of_symbolic_elements_and_sets_is_decided_as_by_comparing_with_each_element() {
        let int = Sort::simple("SortInt");
        let element_sort = Sort::simple("SortKItem");
        let application = |name, argument: Term| {
            Term::application(
                Arc::new(crate::term::Symbol::constructor(
                    name,
                    vec![int.clone()],
                    element_sort.clone(),
                )),
                Vec::new(),
                vec![argument],
            )
        };
        let symbolic = |name| Term::variable(Variable::new(name, int.clone()));
        let one = Term::domain_value(int.clone(), "1");
        let pool = [
            item("0"),
            item("1"),
            item("2"),
            Term::variable(Variable::new("X", element_sort.clone())),
            application("a", symbolic("A")),
            application("a", one.clone()),
            application("b", symbolic("B")),
        ];
        let probes = pool.iter().cloned().chain([
            item("3"),
            Term::variable(Variable::new("Y", element_sort.clone())),
            application("a", symbolic("C")),
            application("b", one),
            application("c", symbolic("D")),
        ]);
        let probes = probes.collect::<Vec<_>>();
        let rest = Term::variable(Variable::new("REST", Sort::simple("SortSet")));
        let mut answers = BTreeMap::<Option<bool>, usize>::new();
        for chosen in 0..1_u32 << pool.len() {
            let elements = pool
                .iter()
                .enumerate()
                .filter(|(index, _)| chosen & (1 << index) != 0)
                .map(|(_, element)| element.clone())
                .collect::<Vec<_>>();
            for rest in [None, Some(rest.clone())] {
                let collection = Term::set(set_definition(), elements.clone(), rest);
                for probed in &probes {
                    let answer = membership(probed, &collection);
                    assert_eq!(
                        answer,
                        membership_by_scan(probed, &collection),
                        "{probed:?} in {collection:?}"
                    );
                    *answers.entry(answer).or_default() += 1;
                }
            }
        }
        assert_eq!(
            answers.keys().copied().collect::<Vec<_>>(),
            [None, Some(false), Some(true)],
            "every outcome is exercised"
        );
    }

    /// In a constructor-like set, `SET.in` compares a constructor-like element with the elements
    /// the binary search visits and with no other: a held element is found by the search, and
    /// one not held differs from every element without being compared with each (`absent`).
    /// The search's own count bounds those comparisons by one binary search per level of the
    /// elements' tree (`Items::search_comparison_bound`).
    #[test]
    fn membership_compares_the_element_only_with_the_elements_the_search_visits() {
        const ELEMENTS: u32 = 4096;
        let texts = (1..=ELEMENTS)
            .map(|index| (2 * index).to_string())
            .collect::<Vec<_>>();
        let collection = set(&texts.iter().map(String::as_str).collect::<Vec<_>>());
        assert!(collection.attributes().constructor_like);
        let TermKind::Set { elements, .. } = collection.kind() else {
            unreachable!("a set term")
        };
        let compared_by = |run: &dyn Fn()| {
            ELEMENT_COMPARISONS.with(|count| count.set(0));
            run();
            ELEMENT_COMPARISONS.with(std::cell::Cell::get)
        };
        let bound = elements.search_comparison_bound();
        for probe in [2, ELEMENTS, 2 * ELEMENTS, 1, ELEMENTS + 1, 2 * ELEMENTS + 1] {
            let probed = item(&probe.to_string());
            let searched = compared_by(&|| {
                let _ = place_of(elements, &probed);
            });
            assert!(
                searched <= bound,
                "element {probe}: the search compares {searched}, bound {bound}"
            );
            let made = compared_by(&|| {
                assert_eq!(
                    super::super::evaluate_hook("SET.in", &[probed.clone(), collection.clone()])
                        .unwrap()
                        .unwrap(),
                    BuiltinResult::Value(bool_term(probe % 2 == 0)),
                    "element {probe}"
                );
            });
            assert_eq!(
                made, searched,
                "element {probe}: {made} elements compared, the search compares {searched}"
            );
        }
    }

    /// The absence of a constructor-like element from a set is decided by comparing it with the
    /// elements that are not constructor-like only: with three such elements among 4,096
    /// constructor applications, `SET.in` of an element of another constructor compares it with
    /// the elements its search visits and the three, and answers as the comparison with each
    /// element does.
    #[test]
    fn absence_of_a_constructor_like_element_compares_it_only_with_the_symbolic_elements() {
        const ELEMENTS: u32 = 4096;
        let int = Sort::simple("SortInt");
        let ground = (0..ELEMENTS)
            .map(|index| applied("c", Term::domain_value(int.clone(), index.to_string())));
        let symbolic = (0..3).map(|index| {
            applied(
                "c",
                Term::variable(Variable::new(format!("X{index}"), int.clone())),
            )
        });
        let collection = Term::set(set_definition(), ground.chain(symbolic).collect(), None);
        let TermKind::Set { elements, .. } = collection.kind() else {
            unreachable!("a set term")
        };
        let probe = applied("d", Term::domain_value(int, "1"));
        ELEMENT_COMPARISONS.with(|count| count.set(0));
        assert_eq!(membership(&probe, &collection), Some(false));
        let compared = ELEMENT_COMPARISONS.with(std::cell::Cell::get);
        assert_eq!(membership_by_scan(&probe, &collection), Some(false));
        let bound = elements.search_comparison_bound() + 3;
        assert!(
            compared <= bound,
            "{compared} elements compared, bound {bound}"
        );
    }

    /// The SET hooks that add, remove or keep a few elements of a large set edit its tree: each
    /// computes the own summaries of at most the elements of the leaves its edits copy (a leaf
    /// and a neighbour each), not one per element of the set, and the result holds the elements
    /// it should.
    #[test]
    fn hooks_that_change_a_few_elements_summarize_only_the_leaves_they_edit() {
        const ELEMENTS: u32 = 4096;
        let leaf = crate::term::chunked::DEFAULT_BRANCHING;
        let numbers = |values: &[u32]| {
            Term::set(
                set_definition(),
                values
                    .iter()
                    .map(|value| item(&value.to_string()))
                    .collect(),
                None,
            )
        };
        let base = numbers(&(1..=ELEMENTS).map(|index| 2 * index).collect::<Vec<_>>());
        let n = ELEMENTS as usize;
        for (name, arguments, size) in [
            ("SET.concat", vec![base.clone(), numbers(&[9])], n + 1),
            ("SET.concat", vec![numbers(&[9]), base.clone()], n + 1),
            ("SET.union", vec![base.clone(), numbers(&[8, 9])], n + 1),
            ("SET.union", vec![numbers(&[8, 9]), base.clone()], n + 1),
            (
                "SET.difference",
                vec![base.clone(), numbers(&[8, 9])],
                n - 1,
            ),
            ("SET.intersection", vec![base.clone(), numbers(&[8, 9])], 1),
            ("SET.intersection", vec![numbers(&[8, 9]), base.clone()], 1),
        ] {
            let mut result = None;
            let summaries = crate::term::items::element_summaries_during(|| {
                result = Some(hook(name, &arguments));
            });
            let Some(BuiltinResult::Value(result)) = result else {
                panic!("{name}: {result:?}");
            };
            let TermKind::Set { elements, .. } = result.kind() else {
                panic!("{name}: {result:?}");
            };
            assert_eq!(elements.len(), size, "{name}");
            assert!(
                summaries <= 2 * leaf,
                "{name}: {summaries} element summaries for one edit of leaves of at most {leaf}"
            );
        }
        assert_eq!(
            hook("SET.concat", &[base.clone(), numbers(&[8])]),
            BuiltinResult::Bottom
        );
        assert_eq!(
            hook("SET.concat", &[numbers(&[2 * ELEMENTS]), base]),
            BuiltinResult::Bottom
        );
    }

    fn hook(name: &str, arguments: &[Term]) -> BuiltinResult {
        super::super::evaluate_hook(name, arguments)
            .unwrap()
            .unwrap()
    }

    /// A constructor application `name(argument)` of sort `KItem` on an `Int`.
    fn applied(name: &str, argument: Term) -> Term {
        Term::application(
            Arc::new(crate::term::Symbol::constructor(
                name,
                vec![Sort::simple("SortInt")],
                Sort::simple("SortKItem"),
            )),
            Vec::new(),
            vec![argument],
        )
    }

    /// The constructor-like element `n` of the pool the union tests draw from: domain values
    /// and constructor applications, so that sets mix kinds of terms.
    fn pooled(n: u8) -> Term {
        if n.is_multiple_of(2) {
            item(&n.to_string())
        } else {
            applied(
                "c",
                Term::domain_value(Sort::simple("SortInt"), n.to_string()),
            )
        }
    }

    /// `S1 |Set S2` as the `domains.md` equation computes it: `S1 (S2 -Set S1)`.
    fn union_by_equation(left: &Term, right: &Term) -> BuiltinResult {
        let BuiltinResult::Value(missing) = hook("SET.difference", &[right.clone(), left.clone()])
        else {
            return BuiltinResult::NotApplicable;
        };
        hook("SET.concat", &[left.clone(), missing])
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

        /// On closed sets of constructor-like elements, the hook gives the set the equation
        /// gives, whether the operands overlap, nest, or are disjoint.
        #[test]
        fn union_of_constructor_like_sets_is_the_equations_set(
            left in proptest::collection::btree_set(0..16_u8, 0..10),
            right in proptest::collection::btree_set(0..16_u8, 0..10),
        ) {
            let build = |chosen: &BTreeSet<u8>| {
                Term::set(set_definition(), chosen.iter().copied().map(pooled).collect(), None)
            };
            let (left_set, right_set) = (build(&left), build(&right));
            let union = hook("SET.union", &[left_set.clone(), right_set.clone()]);
            proptest::prop_assert_eq!(&union, &union_by_equation(&left_set, &right_set));
            proptest::prop_assert_eq!(
                union,
                BuiltinResult::Value(build(&left.union(&right).copied().collect()))
            );
        }
    }

    #[test]
    fn union_keeps_a_common_element_once_and_takes_an_empty_operand_as_no_element() {
        let cases = [
            (set(&["a", "b"]), set(&["b", "c"]), set(&["a", "b", "c"])),
            (set(&["a", "b"]), set(&["a", "b"]), set(&["a", "b"])),
            (set(&["a"]), set(&["a", "b", "c"]), set(&["a", "b", "c"])),
            (
                set(&["a", "c"]),
                set(&["b", "d"]),
                set(&["a", "b", "c", "d"]),
            ),
            (set(&[]), set(&["a"]), set(&["a"])),
            (set(&["a"]), set(&[]), set(&["a"])),
            (set(&[]), set(&[]), set(&[])),
        ];
        for (left, right, expected) in cases {
            assert_eq!(
                hook("SET.union", &[left.clone(), right.clone()]),
                BuiltinResult::Value(expected),
                "{left:?} |Set {right:?}"
            );
        }
    }

    /// An element that may or may not equal one of the other operand's, or a rest whose
    /// elements are not seen, leaves the union's elements undecided: the hook gives no result
    /// and the equation applies as before.
    #[test]
    fn union_with_a_symbolic_element_or_a_rest_gives_no_result() {
        let element_sort = Sort::simple("SortKItem");
        let variable = Term::variable(Variable::new("X", element_sort));
        let symbolic_application = applied(
            "c",
            Term::variable(Variable::new("A", Sort::simple("SortInt"))),
        );
        let rest = Term::variable(Variable::new("REST", Sort::simple("SortSet")));
        let closed = set(&["a", "b"]);
        let undecided = [
            Term::set(set_definition(), vec![variable], None),
            Term::set(
                set_definition(),
                vec![symbolic_application, item("a")],
                None,
            ),
            Term::set(set_definition(), vec![item("c")], Some(rest.clone())),
            Term::set(set_definition(), Vec::new(), Some(rest.clone())),
            rest,
        ];
        for operand in undecided {
            for arguments in [
                [operand.clone(), closed.clone()],
                [closed.clone(), operand.clone()],
            ] {
                assert_eq!(
                    hook("SET.union", &arguments),
                    BuiltinResult::NotApplicable,
                    "{arguments:?}"
                );
            }
        }
    }
}
