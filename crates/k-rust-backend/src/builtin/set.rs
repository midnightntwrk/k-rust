//! Deterministic `SET` hooks implemented by Kore's fallback evaluator.

use std::sync::Arc;

use num_bigint::BigInt;

use super::{BuiltinError, bool_term, expect_arity, int_term};
use crate::{
    builtin::list::k_item_definition as k_item_list_definition,
    term::{CollectionSymbols, SetDefinition, Term, TermKind},
};

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    match hook {
        "SET.concat" => concat(arguments),
        "SET.element" => element(arguments),
        "SET.unit" => unit(arguments),
        "SET.in" => contains(arguments),
        "SET.difference" => difference(arguments),
        "SET.set2list" => to_list(arguments),
        "SET.size" => size(arguments),
        "SET.intersection" => intersection(arguments),
        "SET.list2set" => list_to_set(arguments),
        "SET.inclusion" => inclusion(arguments),
        _ => Ok(None),
    }
}

pub(super) fn k_item_set_definition() -> Arc<SetDefinition> {
    Arc::new(SetDefinition {
        symbols: CollectionSymbols {
            unit: "Lbl'Stop'Set".into(),
            element: "LblSetItem".into(),
            concat: "Lbl'Unds'Set'Unds'".into(),
        },
        element_sort: "SortKItem".into(),
        list_sort: "SortSet".into(),
    })
}

fn concat(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
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
        return Ok(None);
    };
    if left_definition != right_definition || (left_rest.is_some() && right_rest.is_some()) {
        return Ok(None);
    }
    let mut elements = left_elements.clone();
    elements.extend(right_elements.iter().cloned());
    Ok(Some(Term::set(
        left_definition.clone(),
        elements,
        left_rest.clone().or_else(|| right_rest.clone()),
    )))
}

fn element(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("SET.element", arguments, 1)?;
    Ok(Some(Term::set(
        k_item_set_definition(),
        vec![arguments[0].clone()],
        None,
    )))
}

fn unit(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("SET.unit", arguments, 0)?;
    Ok(Some(Term::set(k_item_set_definition(), Vec::new(), None)))
}

fn contains(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("SET.in", arguments, 2)?;
    let [element, set] = arguments else {
        unreachable!()
    };
    if !element.attributes().constructor_like {
        return Ok(None);
    }
    let Some((_, elements)) = concrete_set(set) else {
        return Ok(None);
    };
    Ok(Some(bool_term(elements.binary_search(element).is_ok())))
}

fn difference(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
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
    Ok(Some(Term::set(
        definition.clone(),
        left_elements
            .iter()
            .filter(|element| right_elements.binary_search(element).is_err())
            .cloned()
            .collect(),
        None,
    )))
}

fn to_list(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("SET.set2list", arguments, 1)?;
    let Some((_, elements)) = concrete_set(&arguments[0]) else {
        return Ok(None);
    };
    Ok(Some(Term::list(
        k_item_list_definition(),
        elements.to_vec(),
        None,
    )))
}

fn size(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("SET.size", arguments, 1)?;
    let Some((_, elements)) = concrete_set(&arguments[0]) else {
        return Ok(None);
    };
    Ok(Some(int_term(BigInt::from(elements.len()))))
}

fn intersection(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
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
    Ok(Some(Term::set(
        definition.clone(),
        left_elements
            .iter()
            .filter(|element| right_elements.binary_search(element).is_ok())
            .cloned()
            .collect(),
        None,
    )))
}

fn list_to_set(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("SET.list2set", arguments, 1)?;
    let TermKind::List {
        heads, rest: None, ..
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
    Ok(Some(Term::set(
        k_item_set_definition(),
        heads.clone(),
        None,
    )))
}

fn inclusion(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
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
    use crate::term::{Sort, Variable};

    fn item(value: &str) -> Term {
        Term::domain_value(Sort::simple("SortKItem"), value)
    }

    fn set(values: &[&str]) -> Term {
        Term::set(
            k_item_set_definition(),
            values.iter().map(|value| item(value)).collect(),
            None,
        )
    }

    #[test]
    fn concrete_set_algebra_matches_kore() {
        let left = set(&["a", "b"]);
        let right = set(&["b", "c"]);

        assert_eq!(
            difference(&[left.clone(), right.clone()]),
            Ok(Some(set(&["a"])))
        );
        assert_eq!(
            intersection(&[left.clone(), right.clone()]),
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
            k_item_set_definition(),
            vec![Term::variable(Variable::new(
                "X",
                Sort::simple("SortKItem"),
            ))],
            None,
        );

        assert_eq!(
            contains(&[item("a"), concrete.clone()]),
            Ok(Some(bool_term(true)))
        );
        assert_eq!(
            contains(&[item("c"), concrete.clone()]),
            Ok(Some(bool_term(false)))
        );
        assert_eq!(
            size(std::slice::from_ref(&concrete)),
            Ok(Some(int_term(BigInt::from(2))))
        );
        assert_eq!(contains(&[item("a"), symbolic]), Ok(None));
    }

    #[test]
    fn list_and_set_conversions_are_deterministic() {
        let list = Term::list(
            k_item_list_definition(),
            vec![item("b"), item("a"), item("b")],
            None,
        );
        let expected_set = set(&["a", "b"]);

        assert_eq!(list_to_set(&[list]), Ok(Some(expected_set.clone())));
        assert_eq!(
            to_list(&[expected_set]),
            Ok(Some(Term::list(
                k_item_list_definition(),
                vec![item("a"), item("b")],
                None,
            )))
        );
    }

    #[test]
    fn concat_preserves_one_opaque_remainder() {
        let rest = Term::variable(Variable::new("REST", Sort::simple("SortSet")));
        let left = Term::set(k_item_set_definition(), vec![item("a")], Some(rest.clone()));
        let right = set(&["b"]);

        assert_eq!(
            concat(&[left, right]),
            Ok(Some(Term::set(
                k_item_set_definition(),
                vec![item("a"), item("b")],
                Some(rest)
            )))
        );
    }
}
