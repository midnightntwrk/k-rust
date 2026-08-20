//! Concrete `MAP` hooks implemented by Booster.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use num_bigint::BigInt;

use super::{BuiltinError, BuiltinResult, bool_term, expect_arity, expect_sort, int_term};
use crate::{
    builtin::{list::k_item_definition as k_item_list_definition, set::k_item_set_definition},
    term::{CollectionSymbols, MapDefinition, Term, TermKind},
};

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    let result = match hook {
        "MAP.element" => element(arguments),
        "MAP.unit" => unit(arguments),
        "MAP.update" => update(arguments),
        "MAP.updateAll" => update_all(arguments),
        "MAP.remove" => remove(arguments),
        "MAP.removeAll" => remove_all(arguments),
        "MAP.size" => size(arguments),
        "MAP.lookupOrDefault" => lookup_or_default(arguments),
        "MAP.in_keys" => in_keys(arguments),
        "MAP.keys" => keys(arguments),
        "MAP.keys_list" => keys_list(arguments),
        "MAP.values" => values(arguments),
        "MAP.inclusion" => inclusion(arguments),
        _ => Ok(None),
    }?;
    match hook {
        "MAP.concat" => concat(arguments),
        "MAP.lookup" => lookup(arguments),
        _ => Ok(result.into()),
    }
}

fn k_item_definition() -> Arc<MapDefinition> {
    Arc::new(MapDefinition {
        symbols: CollectionSymbols {
            unit: "Lbl'Stop'Map".into(),
            element: "Lbl'UndsPipe'-'-GT-Unds'".into(),
            concat: "Lbl'Unds'Map'Unds'".into(),
        },
        key_sort: "SortKItem".into(),
        value_sort: "SortKItem".into(),
        map_sort: "SortMap".into(),
    })
}

fn element(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.element", arguments, 2)?;
    Ok(Some(Term::map(
        k_item_definition(),
        vec![(arguments[0].clone(), arguments[1].clone())],
        None,
    )))
}

fn unit(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.unit", arguments, 0)?;
    Ok(Some(Term::map(k_item_definition(), Vec::new(), None)))
}

fn concat(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("MAP.concat", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    let (
        TermKind::Map {
            definition,
            entries: left_entries,
            rest: left_rest,
        },
        TermKind::Map {
            definition: right_definition,
            entries: right_entries,
            rest: right_rest,
        },
    ) = (left.kind(), right.kind())
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if definition != right_definition || (left_rest.is_some() && right_rest.is_some()) {
        return Ok(BuiltinResult::NotApplicable);
    }
    if left_entries.iter().any(|(left_key, _)| {
        right_entries
            .iter()
            .any(|(right_key, _)| left_key == right_key)
    }) {
        return Ok(BuiltinResult::Bottom);
    }
    let mut entries = left_entries.clone();
    entries.extend(right_entries.iter().cloned());
    Ok(BuiltinResult::Value(Term::map(
        definition.clone(),
        entries,
        left_rest.clone().or_else(|| right_rest.clone()),
    )))
}

fn update(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.update", arguments, 3)?;
    let [map, key, new_value] = arguments else {
        unreachable!()
    };
    let TermKind::Map {
        definition,
        entries,
        rest,
    } = map.kind()
    else {
        return Ok(None);
    };
    if let Some(index) = entries
        .iter()
        .position(|(existing_key, _)| existing_key == key)
    {
        let mut updated = entries.clone();
        updated[index] = (key.clone(), new_value.clone());
        return Ok(Some(Term::map(definition.clone(), updated, rest.clone())));
    }
    if rest.is_some()
        || entries
            .iter()
            .any(|(key, _)| !key.attributes().constructor_like)
        || !key.attributes().constructor_like
    {
        return Ok(None);
    }
    let mut updated = vec![(key.clone(), new_value.clone())];
    updated.extend(entries.iter().cloned());
    Ok(Some(Term::map(definition.clone(), updated, None)))
}

fn update_all(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.updateAll", arguments, 2)?;
    let [original, updates] = arguments else {
        unreachable!()
    };
    if let (
        TermKind::Map {
            definition: original_definition,
            ..
        },
        TermKind::Map {
            definition: update_definition,
            ..
        },
    ) = (original.kind(), updates.kind())
        && original_definition != update_definition
    {
        return Err(BuiltinError::IncompatibleMapSorts {
            left: original.sort(),
            right: updates.sort(),
        });
    }
    if matches!(
        updates.kind(),
        TermKind::Map {
            entries,
            rest: None,
            ..
        } if entries.is_empty()
    ) {
        return Ok(Some(original.clone()));
    }
    if matches!(
        original.kind(),
        TermKind::Map {
            entries,
            rest: None,
            ..
        } if entries.is_empty()
    ) {
        return Ok(Some(updates.clone()));
    }
    let (
        TermKind::Map {
            definition,
            entries: original_entries,
            rest: original_rest,
        },
        TermKind::Map {
            entries: update_entries,
            rest: update_rest,
            ..
        },
    ) = (original.kind(), updates.kind())
    else {
        return Ok(None);
    };
    if original_rest.is_some() {
        return Ok(
            (original_entries == update_entries && original_rest == update_rest)
                .then(|| original.clone()),
        );
    }

    let original_map = original_entries.iter().cloned().collect::<BTreeMap<_, _>>();
    let update_map = update_entries.iter().cloned().collect::<BTreeMap<_, _>>();
    let original_keys = original_map.keys().cloned().collect::<BTreeSet<_>>();
    let update_keys = update_map.keys().cloned().collect::<BTreeSet<_>>();
    let untouched_keys = original_keys
        .difference(&update_keys)
        .cloned()
        .collect::<BTreeSet<_>>();
    let added_keys = update_keys
        .difference(&original_keys)
        .cloned()
        .collect::<BTreeSet<_>>();

    let can_apply = untouched_keys.is_empty()
        || (update_rest.is_none()
            && (added_keys.is_empty()
                || untouched_keys
                    .iter()
                    .chain(&added_keys)
                    .all(|key| key.attributes().constructor_like)));
    if !can_apply {
        return Ok(None);
    }

    let mut updated = original_map;
    updated.extend(update_map);
    Ok(Some(Term::map(
        definition.clone(),
        updated.into_iter().collect(),
        update_rest.clone(),
    )))
}

fn remove(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.remove", arguments, 2)?;
    let [map, key] = arguments else {
        unreachable!()
    };
    let TermKind::Map {
        definition,
        entries,
        rest,
    } = map.kind()
    else {
        return Ok(None);
    };
    if let Some(index) = entries
        .iter()
        .position(|(existing_key, _)| existing_key == key)
    {
        let mut updated = entries.clone();
        updated.remove(index);
        return Ok(Some(Term::map(definition.clone(), updated, rest.clone())));
    }
    if rest.is_some()
        || entries
            .iter()
            .any(|(key, _)| !key.attributes().constructor_like)
        || !key.attributes().constructor_like
    {
        Ok(None)
    } else {
        Ok(Some(map.clone()))
    }
}

fn remove_all(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.removeAll", arguments, 2)?;
    let [map, set] = arguments else {
        unreachable!()
    };
    let TermKind::Map {
        definition,
        entries,
        rest: None,
    } = map.kind()
    else {
        return Ok(None);
    };
    let TermKind::Set {
        elements,
        rest: None,
        ..
    } = set.kind()
    else {
        return Ok(None);
    };
    if entries
        .iter()
        .any(|(key, _)| !key.attributes().constructor_like)
        || elements
            .iter()
            .any(|element| !element.attributes().constructor_like)
    {
        return Ok(None);
    }
    Ok(Some(Term::map(
        definition.clone(),
        entries
            .iter()
            .filter(|(key, _)| elements.binary_search(key).is_err())
            .cloned()
            .collect(),
        None,
    )))
}

fn size(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.size", arguments, 1)?;
    let TermKind::Map {
        entries,
        rest: None,
        ..
    } = arguments[0].kind()
    else {
        return Ok(None);
    };
    Ok(Some(int_term(BigInt::from(entries.len()))))
}

fn lookup(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("MAP.lookup", arguments, 2)?;
    let [map, key] = arguments else {
        unreachable!()
    };
    let TermKind::Map { entries, rest, .. } = map.kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if let Some(value) = entries
        .iter()
        .find(|(existing_key, _)| existing_key == key)
        .map(|(_, value)| value.clone())
    {
        return Ok(BuiltinResult::Value(value));
    }
    if rest.is_none()
        && (entries.is_empty()
            || (key.attributes().constructor_like
                && entries
                    .iter()
                    .all(|(key, _)| key.attributes().constructor_like)))
    {
        Ok(BuiltinResult::Bottom)
    } else {
        Ok(BuiltinResult::NotApplicable)
    }
}

fn lookup_or_default(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.lookupOrDefault", arguments, 3)?;
    let [map, key, default] = arguments else {
        unreachable!()
    };
    let TermKind::Map { entries, rest, .. } = map.kind() else {
        return Ok(None);
    };
    if let Some((_, value)) = entries.iter().find(|(existing_key, _)| existing_key == key) {
        return Ok(Some(value.clone()));
    }
    if rest.is_some()
        || entries
            .iter()
            .any(|(key, _)| !key.attributes().constructor_like)
        || !key.attributes().constructor_like
    {
        Ok(None)
    } else {
        Ok(Some(default.clone()))
    }
}

fn in_keys(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.in_keys", arguments, 2)?;
    let [key, map] = arguments else {
        unreachable!()
    };
    let TermKind::Map { entries, rest, .. } = map.kind() else {
        return Ok(None);
    };
    if entries.iter().any(|(existing_key, _)| existing_key == key) {
        return Ok(Some(bool_term(true)));
    }
    if rest.is_none()
        && key.attributes().constructor_like
        && entries
            .iter()
            .all(|(key, _)| key.attributes().constructor_like)
    {
        Ok(Some(bool_term(false)))
    } else {
        Ok(None)
    }
}

fn keys_list(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.keys_list", arguments, 1)?;
    let TermKind::Map {
        entries,
        rest: None,
        ..
    } = arguments[0].kind()
    else {
        return Ok(None);
    };
    Ok(Some(Term::list(
        k_item_list_definition(),
        entries.iter().map(|(key, _)| key.clone()).collect(),
        None,
    )))
}

fn keys(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.keys", arguments, 1)?;
    let TermKind::Map {
        entries,
        rest: None,
        ..
    } = arguments[0].kind()
    else {
        return Ok(None);
    };
    if entries
        .iter()
        .any(|(key, _)| !key.attributes().constructor_like)
    {
        return Ok(None);
    }
    Ok(Some(Term::set(
        k_item_set_definition(),
        entries.iter().map(|(key, _)| key.clone()).collect(),
        None,
    )))
}

fn values(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.values", arguments, 1)?;
    let TermKind::Map {
        entries,
        rest: None,
        ..
    } = arguments[0].kind()
    else {
        return Ok(None);
    };
    Ok(Some(Term::list(
        k_item_list_definition(),
        entries.iter().map(|(_, value)| value.clone()).collect(),
        None,
    )))
}

fn inclusion(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("MAP.inclusion", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    match (left.kind(), right.kind()) {
        (
            TermKind::Map {
                definition: left_definition,
                ..
            },
            TermKind::Map {
                definition: right_definition,
                ..
            },
        ) if left_definition != right_definition => Ok(None),
        (
            TermKind::Map {
                entries: left_entries,
                rest: left_rest,
                ..
            },
            TermKind::Map {
                entries: right_entries,
                rest: right_rest,
                ..
            },
        ) if left_entries == right_entries && left_rest == right_rest => Ok(Some(bool_term(true))),
        (
            TermKind::Map {
                entries: left_entries,
                rest: None,
                ..
            },
            TermKind::Map {
                entries: right_entries,
                rest: right_rest,
                ..
            },
        ) => concrete_inclusion(left_entries, right_entries, right_rest),
        (TermKind::Map { rest: Some(_), .. }, TermKind::Map { .. }) => Ok(None),
        (
            TermKind::Map {
                definition,
                entries,
                rest: None,
            },
            _,
        ) if entries.is_empty() => {
            expect_sort("MAP.inclusion", right, &map_sort(definition))?;
            Ok(Some(bool_term(true)))
        }
        _ if left == right => Ok(Some(bool_term(true))),
        _ => Ok(None),
    }
}

fn concrete_inclusion(
    left_entries: &[(Term, Term)],
    right_entries: &[(Term, Term)],
    right_rest: &Option<Term>,
) -> Result<Option<Term>, BuiltinError> {
    let left_keys = left_entries
        .iter()
        .map(|(key, _)| key)
        .collect::<BTreeSet<_>>();
    let right_keys = right_entries
        .iter()
        .map(|(key, _)| key)
        .collect::<BTreeSet<_>>();
    if left_keys.is_subset(&right_keys) {
        return Ok(Some(bool_term(true)));
    }
    if right_rest.is_none()
        && left_keys
            .iter()
            .chain(&right_keys)
            .all(|key| key.attributes().constructor_like)
    {
        Ok(Some(bool_term(false)))
    } else {
        Ok(None)
    }
}

fn map_sort(definition: &MapDefinition) -> crate::term::Sort {
    crate::term::Sort::simple(definition.map_sort.clone())
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::term::{CollectionSymbols, Sort, Variable};

    fn definition(name: &str) -> Arc<MapDefinition> {
        Arc::new(MapDefinition {
            symbols: CollectionSymbols {
                unit: format!("{name}-unit").into(),
                element: format!("{name}-element").into(),
                concat: format!("{name}-concat").into(),
            },
            key_sort: "SortKey".into(),
            value_sort: "SortValue".into(),
            map_sort: name.into(),
        })
    }

    fn key(value: &str) -> Term {
        Term::domain_value(Sort::simple("SortKey"), value)
    }

    fn value(value: &str) -> Term {
        Term::domain_value(Sort::simple("SortValue"), value)
    }

    #[test]
    fn update_replaces_known_keys_and_adds_certainly_absent_keys() {
        let definition = definition("SortMap");
        let map = Term::map(definition.clone(), vec![(key("a"), value("old"))], None);
        let replaced = Term::map(definition.clone(), vec![(key("a"), value("new"))], None);
        let added = Term::map(
            definition,
            vec![(key("a"), value("old")), (key("b"), value("new"))],
            None,
        );

        assert_eq!(
            update(&[map.clone(), key("a"), value("new")]),
            Ok(Some(replaced))
        );
        assert_eq!(update(&[map, key("b"), value("new")]), Ok(Some(added)));
    }

    #[test]
    fn update_stays_indeterminate_with_symbolic_or_opaque_keys() {
        let definition = definition("SortMap");
        let symbolic_key = Term::variable(Variable::new("K", Sort::simple("SortKey")));
        let symbolic = Term::map(definition.clone(), vec![(symbolic_key, value("old"))], None);
        let rest = Term::variable(Variable::new("REST", Sort::simple("SortMap")));
        let opaque = Term::map(definition, vec![(key("a"), value("old"))], Some(rest));

        assert_eq!(update(&[symbolic, key("b"), value("new")]), Ok(None));
        assert_eq!(update(&[opaque, key("b"), value("new")]), Ok(None));
    }

    #[test]
    fn update_all_overrides_values_and_retains_untouched_entries() {
        let definition = definition("SortMap");
        let original = Term::map(
            definition.clone(),
            vec![(key("a"), value("one")), (key("b"), value("two"))],
            None,
        );
        let updates = Term::map(
            definition.clone(),
            vec![(key("b"), value("changed")), (key("c"), value("three"))],
            None,
        );
        let expected = Term::map(
            definition,
            vec![
                (key("a"), value("one")),
                (key("b"), value("changed")),
                (key("c"), value("three")),
            ],
            None,
        );

        assert_eq!(update_all(&[original, updates]), Ok(Some(expected)));
    }

    #[test]
    fn update_all_rejects_incompatible_collection_definitions() {
        let left = Term::map(definition("SortLeftMap"), Vec::new(), None);
        let right = Term::map(definition("SortRightMap"), Vec::new(), None);

        assert_eq!(
            update_all(&[left, right]),
            Err(BuiltinError::IncompatibleMapSorts {
                left: Sort::simple("SortLeftMap"),
                right: Sort::simple("SortRightMap"),
            })
        );
    }

    #[test]
    fn inclusion_uses_keys_and_requires_constructor_like_absences() {
        let definition = definition("SortMap");
        let left = Term::map(definition.clone(), vec![(key("a"), value("left"))], None);
        let superset = Term::map(
            definition.clone(),
            vec![(key("a"), value("right")), (key("b"), value("two"))],
            None,
        );
        let disjoint = Term::map(definition, vec![(key("c"), value("three"))], None);

        assert_eq!(
            inclusion(&[left.clone(), superset]),
            Ok(Some(bool_term(true)))
        );
        assert_eq!(inclusion(&[left, disjoint]), Ok(Some(bool_term(false))));
    }

    #[test]
    fn remove_lookup_membership_and_size_cover_concrete_maps() {
        let definition = definition("SortMap");
        let map = Term::map(
            definition.clone(),
            vec![(key("a"), value("one")), (key("b"), value("two"))],
            None,
        );
        let removed = Term::map(definition, vec![(key("b"), value("two"))], None);

        assert_eq!(
            lookup(&[map.clone(), key("a")]),
            Ok(BuiltinResult::Value(value("one")))
        );
        assert_eq!(
            lookup_or_default(&[map.clone(), key("missing"), value("default")]),
            Ok(Some(value("default")))
        );
        assert_eq!(in_keys(&[key("a"), map.clone()]), Ok(Some(bool_term(true))));
        assert_eq!(
            in_keys(&[key("missing"), map.clone()]),
            Ok(Some(bool_term(false)))
        );
        assert_eq!(
            size(std::slice::from_ref(&map)),
            Ok(Some(int_term(BigInt::from(2))))
        );
        assert_eq!(remove(&[map, key("a")]), Ok(Some(removed)));
    }

    #[test]
    fn missing_concrete_lookup_and_duplicate_concat_are_bottom() {
        let definition = definition("SortMap");
        let left = Term::map(definition.clone(), vec![(key("a"), value("left"))], None);
        let right = Term::map(definition, vec![(key("a"), value("right"))], None);

        assert_eq!(
            lookup(&[left.clone(), key("missing")]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(concat(&[left, right]), Ok(BuiltinResult::Bottom));
    }

    #[test]
    fn key_sets_and_bulk_removal_match_kore() {
        let definition = definition("SortMap");
        let map = Term::map(
            definition.clone(),
            vec![
                (key("a"), value("one")),
                (key("b"), value("two")),
                (key("c"), value("three")),
            ],
            None,
        );
        let removed_keys = Term::set(k_item_set_definition(), vec![key("a"), key("c")], None);

        assert_eq!(
            keys(std::slice::from_ref(&map)),
            Ok(Some(Term::set(
                k_item_set_definition(),
                vec![key("a"), key("b"), key("c")],
                None,
            )))
        );
        assert_eq!(
            remove_all(&[map, removed_keys]),
            Ok(Some(Term::map(
                definition,
                vec![(key("b"), value("two"))],
                None,
            )))
        );
    }

    #[test]
    fn key_and_value_projections_use_the_reference_kitem_list() {
        let map = Term::map(
            definition("SortMap"),
            vec![(key("b"), value("two")), (key("a"), value("one"))],
            None,
        );
        let expected_keys = Term::list(k_item_list_definition(), vec![key("a"), key("b")], None);
        let expected_values = Term::list(
            k_item_list_definition(),
            vec![value("one"), value("two")],
            None,
        );

        assert_eq!(
            keys_list(std::slice::from_ref(&map)),
            Ok(Some(expected_keys))
        );
        assert_eq!(values(&[map]), Ok(Some(expected_values)));
    }
}
