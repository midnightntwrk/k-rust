//! Concrete `MAP` hooks: per-call operations on the internal map representation; a
//! responsibility, not an algorithm; no counter of its own, no worklist.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;

use super::{
    BuiltinError, BuiltinResult, HookResult, ResultCollection, UnsupportedHookReason, bool_term,
    expect_arity, expect_sort, int_term, values_differ,
};
use crate::{
    matching::SortGraph,
    term::{MapDefinition, Term, TermKind},
};

pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    sorts: Option<&SortGraph>,
    result: ResultCollection<'_>,
) -> HookResult<BuiltinResult> {
    // A hooked application is strict in its arguments, and an internal map that binds a key
    // twice, with the same value or not, is `\bottom` (`Term::map`). A `ceil_free` map has
    // pairwise distinct keys, so only other maps are scanned.
    if arguments
        .iter()
        .any(|argument| !argument.attributes().ceil_free() && argument.repeated_map_key().is_some())
    {
        return Ok(BuiltinResult::Bottom);
    }
    let result = match hook {
        "MAP.element" => element(arguments, result),
        "MAP.unit" => unit(arguments, result),
        "MAP.update" => update(arguments, sorts, result),
        "MAP.updateAll" => update_all(arguments, result),
        "MAP.remove" => remove(arguments, sorts, result),
        "MAP.removeAll" => remove_all(arguments, result),
        "MAP.size" => size(arguments),
        "MAP.lookupOrDefault" => lookup_or_default(arguments, sorts),
        "MAP.in_keys" => in_keys(arguments, sorts),
        "MAP.keys" => keys(arguments, result),
        "MAP.keys_list" => keys_list(arguments, result),
        "MAP.values" => values(arguments, result),
        "MAP.inclusion" => inclusion(arguments),
        "MAP.concat" => return concat(arguments, result),
        "MAP.lookup" => return lookup(arguments, sorts),
        _ => {
            return Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::NotImplemented,
            ));
        }
    }?;
    Ok(result.into())
}

fn element(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("MAP.element", arguments, 2)?;
    let Some(into) = result.map(None) else {
        return Ok(None);
    };
    let (Some(key), Some(value)) = (
        into.key(arguments[0].clone()),
        into.value(arguments[1].clone()),
    ) else {
        return Ok(None);
    };
    Ok(into.build(vec![(key, value)], None))
}

fn unit(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("MAP.unit", arguments, 0)?;
    Ok(result
        .map(None)
        .and_then(|into| into.build(Vec::new(), None)))
}

fn concat(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<BuiltinResult> {
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
    let Some(into) = result.map(Some(definition)) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if left_entries.iter().any(|(left_key, _)| {
        right_entries
            .iter()
            .any(|(right_key, _)| left_key == right_key)
    }) {
        return Ok(BuiltinResult::Bottom);
    }
    let (Some(left_entries), Some(right_entries)) = (
        into.entries(left_entries, definition),
        into.entries(right_entries, definition),
    ) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut entries = left_entries.into_owned();
    entries.extend(right_entries.iter().cloned());
    Ok(into
        .build(entries, left_rest.clone().or_else(|| right_rest.clone()))
        .into())
}

// Without a rest, every possible key is among the entries. Strict operands make
// apartness a difference of values, so a key different from each entry is absent.
fn absent(
    sorts: Option<&SortGraph>,
    key: &Term,
    entries: &[(Term, Term)],
    rest: &Option<Term>,
) -> bool {
    rest.is_none()
        && entries
            .iter()
            .all(|(existing, _)| values_differ(sorts, key, existing))
}

fn update(
    arguments: &[Term],
    sorts: Option<&SortGraph>,
    result: ResultCollection<'_>,
) -> HookResult<Option<Term>> {
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
    // The update is decided on the result's keys: a key argument of a strict subsort of the
    // key sort is compared as the key it is injected to.
    let Some(into) = result.map(Some(definition)) else {
        return Ok(None);
    };
    let (Some(entries), Some(key), Some(new_value)) = (
        into.entries(entries, definition),
        into.key(key.clone()),
        into.value(new_value.clone()),
    ) else {
        return Ok(None);
    };
    if let Some(index) = entries
        .iter()
        .position(|(existing_key, _)| *existing_key == key)
    {
        let mut updated = entries.into_owned();
        updated[index] = (key, new_value);
        return Ok(into.build(updated, rest.clone()));
    }
    if !absent(sorts, &key, &entries, rest) {
        return Ok(None);
    }
    let mut updated = vec![(key, new_value)];
    updated.extend(entries.iter().cloned());
    Ok(into.build(updated, None))
}

fn update_all(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
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
        }
        .into());
    }
    let source = match (original.kind(), updates.kind()) {
        (TermKind::Map { definition, .. }, _) | (_, TermKind::Map { definition, .. }) => {
            Some(definition)
        }
        _ => None,
    };
    let Some(into) = result.map(source) else {
        return Ok(None);
    };
    if matches!(
        updates.kind(),
        TermKind::Map {
            entries,
            rest: None,
            ..
        } if entries.is_empty()
    ) {
        return Ok(into.adopt(original));
    }
    if matches!(
        original.kind(),
        TermKind::Map {
            entries,
            rest: None,
            ..
        } if entries.is_empty()
    ) {
        return Ok(into.adopt(updates));
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
            if original_entries == update_entries && original_rest == update_rest {
                into.adopt(original)
            } else {
                None
            },
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
    let updated = updated.into_iter().collect::<Vec<_>>();
    Ok(into
        .entries(&updated, definition)
        .and_then(|entries| into.build(entries.into_owned(), update_rest.clone())))
}

fn remove(
    arguments: &[Term],
    sorts: Option<&SortGraph>,
    result: ResultCollection<'_>,
) -> HookResult<Option<Term>> {
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
    let Some(into) = result.map(Some(definition)) else {
        return Ok(None);
    };
    let (Some(entries), Some(key)) = (into.entries(entries, definition), into.key(key.clone()))
    else {
        return Ok(None);
    };
    if let Some(index) = entries
        .iter()
        .position(|(existing_key, _)| *existing_key == key)
    {
        let mut updated = entries.into_owned();
        updated.remove(index);
        return Ok(into.build(updated, rest.clone()));
    }
    if !absent(sorts, &key, &entries, rest) {
        Ok(None)
    } else {
        Ok(into.adopt(map))
    }
}

fn remove_all(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
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
    let Some(into) = result.map(Some(definition)) else {
        return Ok(None);
    };
    let kept = entries
        .iter()
        .filter(|(key, _)| elements.binary_search(key).is_err())
        .cloned()
        .collect::<Vec<_>>();
    Ok(into
        .entries(&kept, definition)
        .and_then(|kept| into.build(kept.into_owned(), None)))
}

fn size(arguments: &[Term]) -> HookResult<Option<Term>> {
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

fn lookup(arguments: &[Term], sorts: Option<&SortGraph>) -> HookResult<BuiltinResult> {
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
    if rest.is_none() && (entries.is_empty() || absent(sorts, key, entries, rest)) {
        Ok(BuiltinResult::Bottom)
    } else {
        Ok(BuiltinResult::NotApplicable)
    }
}

fn lookup_or_default(arguments: &[Term], sorts: Option<&SortGraph>) -> HookResult<Option<Term>> {
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
    if !absent(sorts, key, entries, rest) {
        Ok(None)
    } else {
        Ok(Some(default.clone()))
    }
}

fn in_keys(arguments: &[Term], sorts: Option<&SortGraph>) -> HookResult<Option<Term>> {
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
    if absent(sorts, key, entries, rest) {
        Ok(Some(bool_term(false)))
    } else {
        Ok(None)
    }
}

/// The entries of a closed map whose keys are all constructor-like, in key order.
///
/// `keys_list` and `values` may order a map's bindings as the backend likes, but equal maps must
/// give the same order. Constructor-like keys denote different values exactly when they differ,
/// so their syntactic order is an order of the key values. A symbolic key has no place in that
/// order: the syntactic order puts `b` before `X` in `keys_list(X |-> 1 b |-> 2)`, which
/// under `X = a` claims `ListItem(b) ListItem(a)`, while the equal concrete map gives
/// `ListItem(a) ListItem(b)`.
fn ordered_entries(map: &Term) -> Option<(&MapDefinition, &[(Term, Term)])> {
    let TermKind::Map {
        definition,
        entries,
        rest: None,
    } = map.kind()
    else {
        return None;
    };
    entries
        .iter()
        .all(|(key, _)| key.attributes().constructor_like)
        .then_some((definition, entries))
}

fn keys_list(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("MAP.keys_list", arguments, 1)?;
    let Some((definition, entries)) = ordered_entries(&arguments[0]) else {
        return Ok(None);
    };
    let Some(into) = result.list(None) else {
        return Ok(None);
    };
    let keys = entries.iter().map(|(key, _)| key.clone()).collect();
    Ok(into
        .owned_elements(keys, &definition.key_sort)
        .and_then(|keys| into.build(keys, None)))
}

fn keys(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("MAP.keys", arguments, 1)?;
    let TermKind::Map {
        definition,
        entries,
        rest: None,
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
    let Some(into) = result.set(None) else {
        return Ok(None);
    };
    let keys = entries.iter().map(|(key, _)| key.clone()).collect();
    Ok(into
        .owned_elements(keys, &definition.key_sort)
        .and_then(|keys| into.build(keys, None)))
}

fn values(arguments: &[Term], result: ResultCollection<'_>) -> HookResult<Option<Term>> {
    expect_arity("MAP.values", arguments, 1)?;
    let Some((definition, entries)) = ordered_entries(&arguments[0]) else {
        return Ok(None);
    };
    let Some(into) = result.list(None) else {
        return Ok(None);
    };
    let values = entries.iter().map(|(_, value)| value.clone()).collect();
    Ok(into
        .owned_elements(values, &definition.value_sort)
        .and_then(|values| into.build(values, None)))
}

fn inclusion(arguments: &[Term]) -> HookResult<Option<Term>> {
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
        ) => entry_inclusion(left_entries, right_entries, right_rest),
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

fn entry_inclusion(
    left_entries: &[(Term, Term)],
    right_entries: &[(Term, Term)],
    right_rest: &Option<Term>,
) -> HookResult<Option<Term>> {
    let mut undecided = false;
    for (left_key, left_value) in left_entries {
        if let Some((_, right_value)) = right_entries
            .iter()
            .find(|(right_key, _)| left_key == right_key)
        {
            if left_value == right_value {
                continue;
            }
            if left_value.attributes().constructor_like && right_value.attributes().constructor_like
            {
                return Ok(Some(bool_term(false)));
            }
            undecided = true;
            continue;
        }
        if right_rest.is_some()
            || !left_key.attributes().constructor_like
            || right_entries
                .iter()
                .any(|(right_key, _)| !right_key.attributes().constructor_like)
        {
            undecided = true;
            continue;
        }
        return Ok(Some(bool_term(false)));
    }
    Ok((!undecided).then(|| bool_term(true)))
}

fn map_sort(definition: &MapDefinition) -> crate::term::Sort {
    crate::term::Sort::simple(definition.map_sort.clone())
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::term::{
        CollectionMetadata, CollectionSymbols, ListDefinition, SetDefinition, Sort, Variable,
    };

    fn undeclared() -> ResultCollection<'static> {
        ResultCollection::undeclared(None)
    }

    fn into(collection: &CollectionMetadata) -> ResultCollection<'_> {
        ResultCollection::declared(Some(collection), None)
    }

    fn elements(name: &str, element_sort: &str) -> Arc<ListDefinition> {
        Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: format!("{name}-unit").into(),
                element: format!("{name}-element").into(),
                concat: format!("{name}-concat").into(),
            },
            element_sort: element_sort.into(),
            list_sort: name.into(),
        })
    }

    fn key_set_definition() -> Arc<SetDefinition> {
        elements("SortKeySet", "SortKey")
    }

    fn key_list_definition() -> Arc<ListDefinition> {
        elements("SortKeyList", "SortKey")
    }

    fn value_list_definition() -> Arc<ListDefinition> {
        elements("SortValueList", "SortValue")
    }

    fn key_set() -> CollectionMetadata {
        CollectionMetadata::Set(key_set_definition())
    }

    fn key_list() -> CollectionMetadata {
        CollectionMetadata::List(key_list_definition())
    }

    fn value_list() -> CollectionMetadata {
        CollectionMetadata::List(value_list_definition())
    }

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

    fn fu17_map_keys() -> (Term, Term, Term) {
        let int = Sort::simple("SortInt");
        let key_sort = Sort::simple("SortKey");
        let application = |name, variable| {
            Term::application(
                Arc::new(crate::term::Symbol::constructor(
                    name,
                    vec![int.clone()],
                    key_sort.clone(),
                )),
                Vec::new(),
                vec![Term::variable(Variable::new(variable, int.clone()))],
            )
        };
        let a = application("a", "A");
        let b = application("b", "B");
        let map = Term::map(definition("SortMap"), vec![(a.clone(), value("1"))], None);
        (map, a, b)
    }

    #[test]
    fn fu17_in_keys_separates_symbolic_keys() {
        let (map, a, b) = fu17_map_keys();
        assert_eq!(
            super::super::evaluate_hook("MAP.in_keys", &[b, map.clone()])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(bool_term(false))
        );
        assert_eq!(
            super::super::evaluate_hook("MAP.in_keys", &[a, map.clone()])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(bool_term(true))
        );
        let variable = Term::variable(Variable::new("C", Sort::simple("SortKey")));
        assert_eq!(
            super::super::evaluate_hook("MAP.in_keys", &[variable, map])
                .unwrap()
                .unwrap(),
            BuiltinResult::NotApplicable
        );
    }

    #[test]
    fn fu17_lookup_separates_symbolic_keys() {
        let (map, a, b) = fu17_map_keys();
        assert_eq!(
            super::super::evaluate_hook("MAP.lookup", &[map.clone(), b])
                .unwrap()
                .unwrap(),
            BuiltinResult::Bottom
        );
        assert_eq!(
            super::super::evaluate_hook("MAP.lookup", &[map, a])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(value("1"))
        );
    }

    #[test]
    fn fu17_lookup_or_default_separates_symbolic_keys() {
        let (map, _, b) = fu17_map_keys();
        assert_eq!(
            super::super::evaluate_hook("MAP.lookupOrDefault", &[map, b, value("default")])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(value("default"))
        );
    }

    #[test]
    fn fu17_update_separates_symbolic_keys() {
        let (map, a, b) = fu17_map_keys();
        let expected = Term::map(
            definition("SortMap"),
            vec![(a, value("1")), (b.clone(), value("2"))],
            None,
        );
        assert_eq!(
            super::super::evaluate_hook("MAP.update", &[map, b, value("2")])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(expected)
        );
    }

    #[test]
    fn fu17_remove_separates_symbolic_keys() {
        let (map, _, b) = fu17_map_keys();
        assert_eq!(
            super::super::evaluate_hook("MAP.remove", &[map.clone(), b])
                .unwrap()
                .unwrap(),
            BuiltinResult::Value(map)
        );
    }

    #[test]
    fn fu17_map_rest_prevents_absence() {
        let (_, a, b) = fu17_map_keys();
        let map = Term::map(
            definition("SortMap"),
            vec![(a, value("1"))],
            Some(Term::variable(Variable::new(
                "REST",
                Sort::simple("SortMap"),
            ))),
        );
        for (hook, args) in [
            ("MAP.in_keys", vec![b.clone(), map.clone()]),
            ("MAP.lookup", vec![map.clone(), b.clone()]),
            (
                "MAP.lookupOrDefault",
                vec![map.clone(), b.clone(), value("default")],
            ),
            ("MAP.update", vec![map.clone(), b.clone(), value("2")]),
            ("MAP.remove", vec![map, b]),
        ] {
            assert_eq!(
                super::super::evaluate_hook(hook, &args).unwrap().unwrap(),
                BuiltinResult::NotApplicable,
                "{hook}"
            );
        }
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
            update(&[map.clone(), key("a"), value("new")], None, undeclared()),
            Ok(Some(replaced))
        );
        assert_eq!(
            update(&[map, key("b"), value("new")], None, undeclared()),
            Ok(Some(added))
        );
    }

    #[test]
    fn update_stays_indeterminate_with_symbolic_or_opaque_keys() {
        let definition = definition("SortMap");
        let symbolic_key = Term::variable(Variable::new("K", Sort::simple("SortKey")));
        let symbolic = Term::map(definition.clone(), vec![(symbolic_key, value("old"))], None);
        let rest = Term::variable(Variable::new("REST", Sort::simple("SortMap")));
        let opaque = Term::map(definition, vec![(key("a"), value("old"))], Some(rest));

        assert_eq!(
            update(&[symbolic, key("b"), value("new")], None, undeclared()),
            Ok(None)
        );
        assert_eq!(
            update(&[opaque, key("b"), value("new")], None, undeclared()),
            Ok(None)
        );
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

        assert_eq!(
            update_all(&[original, updates], undeclared()),
            Ok(Some(expected))
        );
    }

    #[test]
    fn update_all_rejects_incompatible_collection_definitions() {
        let left = Term::map(definition("SortLeftMap"), Vec::new(), None);
        let right = Term::map(definition("SortRightMap"), Vec::new(), None);

        assert_eq!(
            update_all(&[left, right], undeclared()),
            Err(BuiltinError::IncompatibleMapSorts {
                left: Sort::simple("SortLeftMap"),
                right: Sort::simple("SortRightMap"),
            }
            .into())
        );
    }

    #[test]
    fn inclusion_compares_entries_and_requires_constructor_like_absences() {
        let definition = definition("SortMap");
        let left = Term::map(definition.clone(), vec![(key("a"), value("left"))], None);
        let differing_superset = Term::map(
            definition.clone(),
            vec![(key("a"), value("right")), (key("b"), value("two"))],
            None,
        );
        let matching_superset = Term::map(
            definition.clone(),
            vec![(key("a"), value("left")), (key("b"), value("two"))],
            None,
        );
        let disjoint = Term::map(definition.clone(), vec![(key("c"), value("three"))], None);
        let rest = Term::variable(Variable::new("REST", Sort::simple("SortMap")));
        let differing_with_rest = Term::map(
            definition.clone(),
            vec![(key("a"), value("right"))],
            Some(rest.clone()),
        );
        let missing_with_rest = Term::map(
            definition.clone(),
            vec![(key("b"), value("two"))],
            Some(rest),
        );
        let symbolic_left = Term::map(
            definition.clone(),
            vec![(
                key("a"),
                Term::variable(Variable::new("X", Sort::simple("SortValue"))),
            )],
            None,
        );
        let symbolic_right = Term::map(
            definition.clone(),
            vec![(
                key("a"),
                Term::variable(Variable::new("Y", Sort::simple("SortValue"))),
            )],
            None,
        );
        let open_left = Term::map(
            definition,
            vec![(key("a"), value("left"))],
            Some(Term::variable(Variable::new(
                "LEFT_REST",
                Sort::simple("SortMap"),
            ))),
        );

        assert_eq!(
            inclusion(&[left.clone(), differing_superset]),
            Ok(Some(bool_term(false)))
        );
        assert_eq!(
            inclusion(&[left.clone(), matching_superset]),
            Ok(Some(bool_term(true)))
        );
        assert_eq!(
            inclusion(&[left.clone(), disjoint]),
            Ok(Some(bool_term(false)))
        );
        assert_eq!(
            inclusion(&[left.clone(), differing_with_rest]),
            Ok(Some(bool_term(false)))
        );
        assert_eq!(inclusion(&[left.clone(), missing_with_rest]), Ok(None));
        assert_eq!(inclusion(&[symbolic_left, left.clone()]), Ok(None));
        assert_eq!(inclusion(&[left, symbolic_right]), Ok(None));
        assert_eq!(
            inclusion(&[open_left.clone(), open_left]),
            Ok(Some(bool_term(true)))
        );
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
            lookup(&[map.clone(), key("a")], None),
            Ok(BuiltinResult::Value(value("one")))
        );
        assert_eq!(
            lookup_or_default(&[map.clone(), key("missing"), value("default")], None),
            Ok(Some(value("default")))
        );
        assert_eq!(
            in_keys(&[key("a"), map.clone()], None),
            Ok(Some(bool_term(true)))
        );
        assert_eq!(
            in_keys(&[key("missing"), map.clone()], None),
            Ok(Some(bool_term(false)))
        );
        assert_eq!(
            size(std::slice::from_ref(&map)),
            Ok(Some(int_term(BigInt::from(2))))
        );
        assert_eq!(
            remove(&[map, key("a")], None, undeclared()),
            Ok(Some(removed))
        );
    }

    #[test]
    fn missing_concrete_lookup_and_duplicate_concat_are_bottom() {
        let definition = definition("SortMap");
        let left = Term::map(definition.clone(), vec![(key("a"), value("left"))], None);
        let right = Term::map(definition, vec![(key("a"), value("right"))], None);

        assert_eq!(
            lookup(&[left.clone(), key("missing")], None),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            concat(&[left, right], undeclared()),
            Ok(BuiltinResult::Bottom)
        );
    }

    #[test]
    fn a_map_argument_binding_a_key_twice_makes_the_hook_bottom() {
        let definition = definition("SortMap");
        let same = Term::map(
            definition.clone(),
            vec![(key("a"), value("one")), (key("a"), value("one"))],
            None,
        );
        let different = Term::map(
            definition.clone(),
            vec![(key("a"), value("one")), (key("a"), value("two"))],
            None,
        );
        assert_eq!(same.repeated_map_key(), Some(&key("a")));
        for map in [same, different] {
            assert_eq!(
                evaluate("MAP.size", std::slice::from_ref(&map), None, undeclared()),
                Ok(BuiltinResult::Bottom)
            );
            assert_eq!(
                evaluate(
                    "MAP.update",
                    &[map, key("b"), value("three")],
                    None,
                    undeclared()
                ),
                Ok(BuiltinResult::Bottom)
            );
        }
        let single = Term::map(definition, vec![(key("a"), value("one"))], None);
        assert_eq!(
            evaluate("MAP.concat", &[single.clone(), single], None, undeclared()),
            Ok(BuiltinResult::Bottom)
        );
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
        let removed_keys = Term::set(key_set_definition(), vec![key("a"), key("c")], None);

        assert_eq!(
            keys(std::slice::from_ref(&map), into(&key_set())),
            Ok(Some(Term::set(
                key_set_definition(),
                vec![key("a"), key("b"), key("c")],
                None,
            )))
        );
        assert_eq!(
            remove_all(&[map, removed_keys], undeclared()),
            Ok(Some(Term::map(
                definition,
                vec![(key("b"), value("two"))],
                None,
            )))
        );
    }

    /// The order of `keys_list` and `values` must be a function of the map's value; with a
    /// symbolic key it would follow the key's syntax instead.
    #[test]
    fn key_and_value_projections_wait_for_constructor_like_keys() {
        let symbolic = Term::variable(Variable::new("K", Sort::simple("SortKey")));
        let map = Term::map(
            definition("SortMap"),
            vec![(symbolic, value("one")), (key("b"), value("two"))],
            None,
        );

        assert_eq!(
            keys_list(std::slice::from_ref(&map), into(&key_list())),
            Ok(None)
        );
        assert_eq!(values(&[map], into(&value_list())), Ok(None));
    }

    #[test]
    fn key_and_value_projections_are_kitem_lists_in_key_order() {
        let map = Term::map(
            definition("SortMap"),
            vec![(key("b"), value("two")), (key("a"), value("one"))],
            None,
        );
        let expected_keys = Term::list(key_list_definition(), vec![key("a"), key("b")], None);
        let expected_values = Term::list(
            value_list_definition(),
            vec![value("one"), value("two")],
            None,
        );

        assert_eq!(
            keys_list(std::slice::from_ref(&map), into(&key_list())),
            Ok(Some(expected_keys))
        );
        assert_eq!(
            values(&[map], into(&value_list())),
            Ok(Some(expected_values))
        );
    }
}
