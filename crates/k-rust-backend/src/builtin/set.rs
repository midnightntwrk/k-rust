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
    term::{SetDefinition, Term, TermKind},
};

pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    sorts: Option<&SortGraph>,
    result: ResultCollection<'_>,
) -> HookResult<BuiltinResult> {
    // A hooked application is strict in its arguments, and an internal set that holds an
    // element twice is `\bottom`: set concatenation is nilpotent (`Term::set`). A `ceil_free`
    // set has pairwise distinct elements, so only other sets are scanned; the hooks below
    // already visit every element of a set they compute on.
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
    // Both element lists are sorted (`Term::set`), so one merge pass finds a shared element.
    let (mut left_index, mut right_index) = (0, 0);
    while let (Some(left), Some(right)) = (
        left_elements.get(left_index),
        right_elements.get(right_index),
    ) {
        match left.cmp(right) {
            std::cmp::Ordering::Less => left_index += 1,
            std::cmp::Ordering::Greater => right_index += 1,
            std::cmp::Ordering::Equal => return Ok(BuiltinResult::Bottom),
        }
    }
    let from = &left_definition.element_sort;
    let (Some(left_elements), Some(right_elements)) = (
        into.elements(left_elements, from),
        into.elements(right_elements, from),
    ) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut elements = left_elements.into_owned();
    elements.extend(right_elements.iter().cloned());
    Ok(into
        .build(elements, left_rest.clone().or_else(|| right_rest.clone()))
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
    if elements.contains(element) {
        Ok(Some(bool_term(true)))
    } else if rest.is_none()
        && elements
            .iter()
            .all(|existing| values_differ(sorts, element, existing))
    {
        Ok(Some(bool_term(false)))
    } else {
        Ok(None)
    }
}

/// The set of the elements of `definition`'s concrete set `left` that `keep` admits, in the
/// result's collection.
fn filtered(
    result: ResultCollection<'_>,
    definition: &Arc<SetDefinition>,
    left: &[Term],
    keep: impl Fn(&Term) -> bool,
) -> Option<Term> {
    let into = result.set(Some(definition))?;
    let kept = left
        .iter()
        .filter(|element| keep(element))
        .cloned()
        .collect();
    let kept = into.owned_elements(kept, &definition.element_sort)?;
    into.build(kept, None)
}

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
    Ok(filtered(result, definition, left_elements, |element| {
        right_elements.binary_search(element).is_err()
    }))
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
        .and_then(|elements| into.build(elements.into_owned(), None)))
}

fn size(arguments: &[Term]) -> HookResult<Option<Term>> {
    expect_arity("SET.size", arguments, 1)?;
    let Some((_, elements)) = concrete_set(&arguments[0]) else {
        return Ok(None);
    };
    Ok(Some(int_term(BigInt::from(elements.len()))))
}

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
    Ok(filtered(result, definition, left_elements, |element| {
        right_elements.binary_search(element).is_ok()
    }))
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
    let Some(elements) = into.elements(heads, &definition.element_sort) else {
        return Ok(None);
    };
    let mut elements = elements.into_owned();
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
    Ok(Some(bool_term(left_elements.iter().all(|element| {
        right_elements.binary_search(element).is_ok()
    }))))
}

fn concrete_set(term: &Term) -> Option<(&Arc<SetDefinition>, &[Term])> {
    let TermKind::Set {
        definition,
        elements,
        rest: None,
    } = term.kind()
    else {
        return None;
    };
    elements
        .iter()
        .all(|element| element.attributes().constructor_like)
        .then_some((definition, elements))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{CollectionMetadata, CollectionSymbols, ListDefinition, Sort, Variable};

    fn shape(name: &str) -> Arc<ListDefinition> {
        Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: format!("{name}-unit").into(),
                element: format!("{name}-element").into(),
                concat: format!("{name}-concat").into(),
            },
            element_sort: "SortKItem".into(),
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
}
