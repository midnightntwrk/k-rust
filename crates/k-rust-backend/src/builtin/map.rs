//! Concrete `MAP` hooks: per-call operations on the internal map representation; a
//! responsibility, not an algorithm; no counter of its own, no worklist.
//!
//! Each hook is a few operations of the persistent tree that holds the map's entries (card
//! `backend.term.chunked`), so for a map argument of `n` entries, `s` of them with a key that is
//! not constructor-like, and `m` items in the other collection argument (the smaller operand of
//! `concat`):
//!
//! - `size`: `O(1)`, the root summary's count; `element`, `unit`: `O(1)`.
//! - `lookup`, `lookupOrDefault`, `in_keys`: one search, `O(log n)`. A key the search does not find
//!   is decided absent by `absent`: a constructor-like key is compared with the `s` other keys
//!   only, `O(s log n)`; a key that is not constructor-like with every entry, `O(n)`.
//! - `update`, `remove`: one search and one path copy, `O(log n)`.
//! - `updateAll`, `removeAll`: one search and one path copy per item of the second argument,
//!   `O(m log n)`; `inclusion`: one search in the right map per entry of the left, `O(m log n)`.
//! - `concat`: the union of the two trees, `O(m log(n/m + 1))`, a repeated key read from the
//!   union's summary.
//! - `keys`, `keys_list`, `values`: `O(n)`, the size of the result.

use std::borrow::Cow;

use num_bigint::BigInt;

use super::{
    BuiltinError, BuiltinResult, HookResult, ResultCollection, UnsupportedHookReason, bool_term,
    expect_arity, expect_sort, int_term, result_collection::MapResult, values_differ,
};
use crate::{
    matching::SortGraph,
    term::{Items, MapDefinition, Term, TermKind, chunked::Item},
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
    // A key both operands bind makes the concatenation `\bottom`. Each operand binds a key
    // once (`evaluate`) and holds its entries ordered by key, so in the ordered union of the two
    // the entries of a key both bind stand side by side, which the union's summary records
    // (`collision`): the check costs the union, `O(m log(n/m + 1))` nodes for operands of `n`
    // and `m` entries, rather than a comparison of every pair of keys.
    let united = left_entries.union(right_entries);
    if united.summary().collision {
        return Ok(BuiltinResult::Bottom);
    }
    Ok(into
        .build_from(
            Cow::Owned(united),
            definition,
            left_rest.clone().or_else(|| right_rest.clone()),
        )
        .into())
}

/// The place of `key` among the keys of `entries`, syntactically: `Ok` with the index of the
/// entry that binds it, or `Err` with the index at which an entry binding it would go.
///
/// `entries` are the entries of a map argument as `Term::map` stores them, sorted by
/// `(key, value)`, and `evaluate` answers `\bottom` before a hook sees a map that binds a key
/// twice, so the keys are strictly increasing and the order of `Term` decides both whether
/// `key` is among them and where: a binary search finds it in `O(log n)` comparisons.
fn place_of<K: Ord, V>(entries: &Items<(K, V)>, key: &K) -> Result<usize, usize>
where
    (K, V): Item,
{
    entries.search_by(|(existing, _)| {
        #[cfg(test)]
        compared_with_an_entry();
        existing.cmp(key)
    })
}

#[cfg(test)]
thread_local! {
    /// Test builds: the entries of a stored map this thread's `MAP` hooks have compared a key
    /// with, by the search (`place_of`) or entry by entry (`absent`).
    static ENTRY_COMPARISONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn compared_with_an_entry() {
    ENTRY_COMPARISONS.with(|count| count.set(count.get() + 1));
}

/// The index of the entry of `entries` whose key is `key`, syntactically (`place_of`).
fn bound_at<K: Ord, V>(entries: &Items<(K, V)>, key: &K) -> Option<usize>
where
    (K, V): Item,
{
    place_of(entries, key).ok()
}

/// Whether `key`, which binds none of `entries` syntactically, is bound nowhere in the map.
///
/// Without a rest, every possible key is among the entries. Strict operands make apartness a
/// difference of values, so a key different from each entry's key is absent. Two
/// constructor-like terms denote different values exactly when they differ syntactically, so a
/// constructor-like key differs from every constructor-like key of the entries already, and is
/// compared only with the keys that are not constructor-like: the entries' summary counts them
/// and leads to them (`Items::symbolic_keyed`), `O(s log n)` nodes for `s` such keys among `n`.
/// A key that is not constructor-like is compared with each entry.
fn absent(
    sorts: Option<&SortGraph>,
    key: &Term,
    entries: &Items<(Term, Term)>,
    rest: &Option<Term>,
) -> bool {
    let differs = |(existing, _): &(Term, Term)| {
        #[cfg(test)]
        compared_with_an_entry();
        values_differ(sorts, key, existing)
    };
    rest.is_none()
        && if key.attributes().constructor_like {
            entries.symbolic_keyed().all(differs)
        } else {
            entries.iter().all(differs)
        }
}

/// The result map of `entries`, edited from a map argument's entries as the result's sorts
/// give them (`MapResult::entries`): the argument's own (`stored`), whose edits keep their
/// order and their tree, or converted ones, which are ordered again.
fn built(
    into: MapResult<'_>,
    entries: Items<(Term, Term)>,
    stored: bool,
    rest: Option<Term>,
) -> Option<Term> {
    if stored {
        into.build_ordered(entries, rest)
    } else {
        into.build(entries.into(), rest)
    }
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
    // Entries of the result's sorts are the argument's own, in their stored order (`place_of`);
    // entries injected into the result's sorts may not keep that order, and are scanned.
    let stored = matches!(entries, Cow::Borrowed(_));
    let place = if stored {
        place_of(&entries, &key)
    } else {
        entries
            .iter()
            .position(|(existing_key, _)| *existing_key == key)
            .ok_or(entries.len())
    };
    match place {
        Ok(index) => {
            let updated = entries.replace_at(index, (key, new_value));
            Ok(built(into, updated, stored, rest.clone()))
        }
        Err(index) => {
            if !absent(sorts, &key, &entries, rest) {
                return Ok(None);
            }
            let updated = entries.insert_at(index, (key, new_value));
            Ok(built(into, updated, stored, None))
        }
    }
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

    // Each binding of the updates replaces the original's binding of its key or is added: the
    // original without the keys the updates bind, united with the updates. Each update key is
    // searched among the original's, and the original's binding of it removed, so the result
    // costs `O(log n)` nodes per update binding and the union, and shares the rest of both
    // trees. The keys both bind (`shared`) say which keys the updates leave untouched and which
    // they add, and the entries' summaries how many of each are not constructor-like.
    let mut kept = original_entries.clone();
    let (mut shared, mut shared_symbolic) = (0, 0);
    for (key, _) in update_entries {
        if let Some(index) = bound_at(&kept, key) {
            kept = kept.remove_at(index).0;
            shared += 1;
            shared_symbolic += usize::from(!key.attributes().constructor_like);
        }
    }
    let untouched = original_entries.len() - shared;
    let added = update_entries.len() - shared;
    let untouched_and_added_constructor_like = original_entries.symbolic_keys() == shared_symbolic
        && update_entries.symbolic_keys() == shared_symbolic;
    let can_apply = untouched == 0
        || (update_rest.is_none() && (added == 0 || untouched_and_added_constructor_like));
    if !can_apply {
        return Ok(None);
    }
    Ok(into.build_from(
        Cow::Owned(kept.union(update_entries)),
        definition,
        update_rest.clone(),
    ))
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
    let stored = matches!(entries, Cow::Borrowed(_));
    let index = if stored {
        bound_at(&entries, &key)
    } else {
        entries
            .iter()
            .position(|(existing_key, _)| *existing_key == key)
    };
    if let Some(index) = index {
        let (updated, _) = entries.remove_at(index);
        return Ok(built(into, updated, stored, rest.clone()));
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
        definition: set_definition,
        elements,
        rest: None,
    } = set.kind()
    else {
        return Ok(None);
    };
    // The set's elements are compared with the keys as terms, which says whether they are the
    // same key only when both are of one sort: a key of a narrower sort is held injected in the
    // set and bare in the map.
    if set_definition.element_sort != definition.key_sort {
        return Ok(None);
    }
    if entries.symbolic_keys() > 0 || elements.symbolic_keys() > 0 {
        return Ok(None);
    }
    let Some(into) = result.map(Some(definition)) else {
        return Ok(None);
    };
    // One removal per element the map binds, each a search and a path copy, `O(log n)` nodes.
    let mut kept = entries.clone();
    for element in elements {
        if let Some(index) = bound_at(&kept, element) {
            kept = kept.remove_at(index).0;
        }
    }
    Ok(into.build_from(Cow::Owned(kept), definition, None))
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
    if let Some(index) = bound_at(entries, key) {
        let (_, value) = entries.get(index).expect("a bound key's entry");
        return Ok(BuiltinResult::Value(value.clone()));
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
    if let Some(index) = bound_at(entries, key) {
        let (_, value) = entries.get(index).expect("a bound key's entry");
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
    if bound_at(entries, key).is_some() {
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
fn ordered_entries(map: &Term) -> Option<(&MapDefinition, &Items<(Term, Term)>)> {
    let TermKind::Map {
        definition,
        entries,
        rest: None,
    } = map.kind()
    else {
        return None;
    };
    (entries.symbolic_keys() == 0).then_some((definition, entries))
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
    if entries.symbolic_keys() > 0 {
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

/// Whether each binding of a closed left map is a binding of the right one, or `None` when that
/// is not decided. Each left key is searched among the right keys (`bound_at`: the right map
/// binds each key once), `O(log m)`, and whether every right key is constructor-like is read
/// from the right entries' summary.
fn entry_inclusion(
    left_entries: &Items<(Term, Term)>,
    right_entries: &Items<(Term, Term)>,
    right_rest: &Option<Term>,
) -> HookResult<Option<Term>> {
    let right_keys_constructor_like = right_entries.symbolic_keys() == 0;
    let mut undecided = false;
    for (left_key, left_value) in left_entries {
        if let Some((_, right_value)) =
            bound_at(right_entries, left_key).and_then(|index| right_entries.get(index))
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
            || !right_keys_constructor_like
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
    use std::{cell::Cell, collections::BTreeMap, sync::Arc};

    use super::*;
    use crate::counted::Counted;
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
            element_sort: Sort::simple(element_sort),
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
            key_sort: Sort::simple("SortKey"),
            value_sort: Sort::simple("SortValue"),
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

    fn hook(name: &str, arguments: &[Term]) -> BuiltinResult {
        super::super::evaluate_hook(name, arguments)
            .unwrap()
            .unwrap()
    }

    fn bindings_map(definition: &Arc<MapDefinition>, bindings: &BTreeMap<u32, u32>) -> Term {
        Term::map(
            definition.clone(),
            bindings
                .iter()
                .map(|(bound, to)| (key(&bound.to_string()), value(&to.to_string())))
                .collect(),
            None,
        )
    }

    /// Maps of every size up to 33 bind `2i` to `2i + 1`; each hook that reads or changes one
    /// key is applied at every bound key and at every key before, between and after them, and
    /// answers what the bindings say. The keys' text order (`"10"` before `"2"`) is not their
    /// numeric order, and the search follows the terms' order, not the numbers'.
    #[test]
    fn one_key_hooks_answer_the_bindings_at_every_place_in_maps_of_every_size() {
        let definition = definition("SortMap");
        for size in 0..=33_u32 {
            let bindings = (0..size)
                .map(|index| (2 * index, 2 * index + 1))
                .collect::<BTreeMap<_, _>>();
            let map = bindings_map(&definition, &bindings);
            for probe in 0..=2 * size + 1 {
                let probed = key(&probe.to_string());
                let bound = bindings.get(&probe).map(|to| value(&to.to_string()));
                let case = format!("size {size}, key {probe}");
                assert_eq!(
                    hook("MAP.lookup", &[map.clone(), probed.clone()]),
                    bound
                        .clone()
                        .map_or(BuiltinResult::Bottom, BuiltinResult::Value),
                    "{case}"
                );
                assert_eq!(
                    hook(
                        "MAP.lookupOrDefault",
                        &[map.clone(), probed.clone(), value("default")]
                    ),
                    BuiltinResult::Value(bound.clone().unwrap_or_else(|| value("default"))),
                    "{case}"
                );
                assert_eq!(
                    hook("MAP.in_keys", &[probed.clone(), map.clone()]),
                    BuiltinResult::Value(bool_term(bound.is_some())),
                    "{case}"
                );
                let mut updated = bindings.clone();
                updated.insert(probe, 1000);
                assert_eq!(
                    hook("MAP.update", &[map.clone(), probed.clone(), value("1000")]),
                    BuiltinResult::Value(bindings_map(&definition, &updated)),
                    "{case}"
                );
                let mut removed = bindings.clone();
                removed.remove(&probe);
                assert_eq!(
                    hook("MAP.remove", &[map.clone(), probed]),
                    BuiltinResult::Value(bindings_map(&definition, &removed)),
                    "{case}"
                );
            }
        }
    }

    /// Every one-key hook finds its key in a stored map with `place_of`, a search over the
    /// strictly increasing keys: a key bound in the map and a key that would go before, between or
    /// after its keys are each placed with at most the comparisons of one binary search per node
    /// on a path of the entries' tree (`Items::search_comparison_bound`), logarithmic in the
    /// number of entries, not one comparison per entry.
    #[test]
    fn a_key_is_placed_among_the_stored_entries_by_binary_search() {
        const ENTRIES: u32 = 4096;
        let comparisons = Cell::new(0);
        let counted = |value| Counted {
            value,
            comparisons: &comparisons,
        };
        let entries = (1..=ENTRIES)
            .map(|index| (counted(2 * index), index))
            .collect::<Items<_>>();
        let bound = entries.search_comparison_bound();
        for (probe, expected) in [
            (2, Ok(0)),
            (2 * ENTRIES / 2, Ok(ENTRIES as usize / 2 - 1)),
            (2 * ENTRIES, Ok(ENTRIES as usize - 1)),
            (1, Err(0)),
            (ENTRIES + 1, Err(ENTRIES as usize / 2)),
            (2 * ENTRIES + 1, Err(ENTRIES as usize)),
        ] {
            let probed = counted(probe);
            comparisons.set(0);
            let place = place_of(&entries, &probed);
            let made = comparisons.get();
            assert_eq!(place, expected, "key {probe}");
            assert!(
                made <= bound,
                "key {probe}: {made} comparisons, bound {bound}"
            );
            comparisons.set(0);
            assert_eq!(bound_at(&entries, &probed), expected.ok(), "key {probe}");
            let made = comparisons.get();
            assert!(
                made <= bound,
                "key {probe}: {made} comparisons, bound {bound}"
            );
        }
    }

    /// In a constructor-like map, a hook that reads or changes one key compares it with the
    /// entries the binary search visits and with no other: a bound key is found by the search,
    /// and an unbound one, constructor-like too, differs from every entry without being compared
    /// with each (`absent`). Each hook therefore makes exactly the comparisons `place_of` makes
    /// alone, which the search's own count bounds
    /// (`a_key_is_placed_among_the_stored_entries_by_binary_search`).
    #[test]
    fn a_one_key_hook_compares_its_key_only_with_the_entries_the_search_visits() {
        const ENTRIES: u32 = 4096;
        let definition = definition("SortMap");
        let bindings = (1..=ENTRIES)
            .map(|index| (2 * index, 2 * index + 1))
            .collect::<BTreeMap<_, _>>();
        let map = bindings_map(&definition, &bindings);
        assert!(map.attributes().constructor_like);
        let TermKind::Map { entries, .. } = map.kind() else {
            unreachable!("a map term")
        };
        let compared_by = |run: &dyn Fn()| {
            ENTRY_COMPARISONS.with(|count| count.set(0));
            run();
            ENTRY_COMPARISONS.with(Cell::get)
        };
        for probe in [2, ENTRIES, 2 * ENTRIES, 1, ENTRIES + 1, 2 * ENTRIES + 1] {
            let probed = key(&probe.to_string());
            let searched = compared_by(&|| {
                let _ = place_of(entries, &probed);
            });
            for (name, arguments) in [
                ("MAP.lookup", vec![map.clone(), probed.clone()]),
                (
                    "MAP.lookupOrDefault",
                    vec![map.clone(), probed.clone(), value("0")],
                ),
                ("MAP.in_keys", vec![probed.clone(), map.clone()]),
                ("MAP.update", vec![map.clone(), probed.clone(), value("0")]),
                ("MAP.remove", vec![map.clone(), probed.clone()]),
            ] {
                let made = compared_by(&|| {
                    assert_ne!(
                        hook(name, &arguments),
                        BuiltinResult::NotApplicable,
                        "{name} at key {probe}"
                    );
                });
                assert_eq!(
                    made, searched,
                    "{name} at key {probe}: {made} entries compared, the search compares {searched}"
                );
            }
        }
    }

    /// Absence is decided without comparing the key with each entry only when the key and every
    /// entry are constructor-like. A symbolic value leaves the keys constructor-like, and each
    /// entry still separates an unbound ground key; a symbolic key among ground ones may be any
    /// key, so an unbound ground key stays undecided while a bound one is still found.
    #[test]
    fn a_map_that_is_not_constructor_like_decides_absence_entry_by_entry() {
        let definition = definition("SortMap");
        let symbolic_value = Term::variable(Variable::new("V", Sort::simple("SortValue")));
        let symbolic_key = Term::variable(Variable::new("K", Sort::simple("SortKey")));
        let mut ground = (0..20_u32)
            .map(|index| (key(&(2 * index).to_string()), value("1")))
            .collect::<Vec<_>>();
        ground[7].1 = symbolic_value.clone();
        let symbolic_values = Term::map(definition.clone(), ground.clone(), None);
        assert!(!symbolic_values.attributes().constructor_like);
        assert_eq!(
            hook("MAP.in_keys", &[key("15"), symbolic_values.clone()]),
            BuiltinResult::Value(bool_term(false))
        );
        assert_eq!(
            hook("MAP.lookup", &[symbolic_values.clone(), key("14")]),
            BuiltinResult::Value(symbolic_value)
        );
        assert_eq!(
            hook("MAP.lookup", &[symbolic_values, key("15")]),
            BuiltinResult::Bottom
        );

        ground[7].1 = value("1");
        ground.push((symbolic_key, value("2")));
        let symbolic_keys = Term::map(definition, ground, None);
        for (name, arguments) in [
            ("MAP.in_keys", vec![key("15"), symbolic_keys.clone()]),
            ("MAP.lookup", vec![symbolic_keys.clone(), key("15")]),
            (
                "MAP.lookupOrDefault",
                vec![symbolic_keys.clone(), key("15"), value("0")],
            ),
            (
                "MAP.update",
                vec![symbolic_keys.clone(), key("15"), value("3")],
            ),
            ("MAP.remove", vec![symbolic_keys.clone(), key("15")]),
        ] {
            assert_eq!(
                hook(name, &arguments),
                BuiltinResult::NotApplicable,
                "{name}"
            );
        }
        assert_eq!(
            hook("MAP.in_keys", &[key("14"), symbolic_keys.clone()]),
            BuiltinResult::Value(bool_term(true))
        );
        assert_eq!(
            hook("MAP.lookup", &[symbolic_keys, key("14")]),
            BuiltinResult::Value(value("1"))
        );
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

    /// A set of another element sort holds a key differently from the map (injected, not bare),
    /// so comparing them as terms would keep keys the set names; the removal is left unevaluated.
    #[test]
    fn bulk_removal_waits_for_a_set_of_the_key_sort() {
        let map = Term::map(
            definition("SortMap"),
            vec![(key("a"), value("one")), (key("b"), value("two"))],
            None,
        );
        let wider = Term::set(elements("SortKItemSet", "SortKItem"), vec![key("a")], None);

        assert_eq!(remove_all(&[map, wider], undeclared()), Ok(None));
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

    /// A hook that changes a few bindings of a large map copies the paths to them and shares
    /// the rest of the map's tree: it summarizes only the entries of the leaves it rebuilds, each
    /// edit at most the leaf it edits and one neighbour it merges with or cuts off, whatever the
    /// map's size. Concatenation's check that the operands bind no key twice is read from the
    /// summary of their union, and an operand binding a key of the other is still `\bottom`.
    #[test]
    fn hooks_that_change_a_few_bindings_summarize_only_the_leaves_they_edit() {
        const ENTRIES: u32 = 4096;
        let leaf = crate::term::chunked::DEFAULT_BRANCHING;
        let definition = definition("SortMap");
        let bindings = (1..=ENTRIES)
            .map(|index| (2 * index, 2 * index + 1))
            .collect::<BTreeMap<_, _>>();
        let map = bindings_map(&definition, &bindings);
        let one = |bound: u32| bindings_map(&definition, &BTreeMap::from([(bound, 0)]));
        let key_set =
            |bound: u32| Term::set(key_set_definition(), vec![key(&bound.to_string())], None);
        for (name, arguments, edits, size) in [
            (
                "MAP.update",
                vec![map.clone(), key("8"), value("0")],
                1,
                ENTRIES,
            ),
            (
                "MAP.update",
                vec![map.clone(), key("9"), value("0")],
                1,
                ENTRIES + 1,
            ),
            ("MAP.remove", vec![map.clone(), key("8")], 1, ENTRIES - 1),
            ("MAP.concat", vec![map.clone(), one(9)], 1, ENTRIES + 1),
            ("MAP.concat", vec![one(9), map.clone()], 1, ENTRIES + 1),
            ("MAP.updateAll", vec![map.clone(), one(8)], 2, ENTRIES),
            ("MAP.updateAll", vec![map.clone(), one(9)], 2, ENTRIES + 1),
            (
                "MAP.removeAll",
                vec![map.clone(), key_set(8)],
                1,
                ENTRIES - 1,
            ),
            ("MAP.removeAll", vec![map.clone(), key_set(9)], 1, ENTRIES),
        ] {
            let mut result = None;
            let summaries = crate::term::items::entry_summaries_during(|| {
                result = Some(hook(name, &arguments));
            });
            let Some(BuiltinResult::Value(result)) = result else {
                panic!("{name}: {result:?}");
            };
            let TermKind::Map { entries, .. } = result.kind() else {
                panic!("{name}: {result:?}");
            };
            assert_eq!(entries.len(), size as usize, "{name}");
            assert!(
                summaries <= 2 * leaf * edits,
                "{name}: {summaries} entry summaries for {edits} edits of leaves of at most {leaf}"
            );
        }
        assert_eq!(
            hook("MAP.concat", &[map.clone(), one(8)]),
            BuiltinResult::Bottom
        );
        assert_eq!(
            hook("MAP.concat", &[one(2 * ENTRIES), map]),
            BuiltinResult::Bottom
        );
    }

    /// A constructor-like key that binds no entry differs from every constructor-like key, so
    /// absence compares it only with the keys that are not constructor-like, which the entries'
    /// summary leads to: none when only values are symbolic, one for one symbolic key.
    #[test]
    fn absence_of_a_ground_key_compares_it_only_with_the_symbolic_keys() {
        const ENTRIES: u32 = 4096;
        let definition = definition("SortMap");
        let mut entries = (1..=ENTRIES)
            .map(|index| (key(&(2 * index).to_string()), value("1")))
            .collect::<Vec<_>>();
        entries[100].1 = Term::variable(Variable::new("V", Sort::simple("SortValue")));
        let symbolic_values = Term::map(definition.clone(), entries.clone(), None);
        assert!(!symbolic_values.attributes().constructor_like);
        entries[100].1 = value("1");
        entries.push((
            Term::variable(Variable::new("K", Sort::simple("SortKey"))),
            value("2"),
        ));
        let symbolic_key = Term::map(definition, entries, None);
        let TermKind::Map {
            entries: stored, ..
        } = symbolic_values.kind()
        else {
            unreachable!("a map term")
        };
        let probe = key("15");
        let compared_by = |run: &dyn Fn()| {
            ENTRY_COMPARISONS.with(|count| count.set(0));
            run();
            ENTRY_COMPARISONS.with(Cell::get)
        };
        let searched = compared_by(&|| {
            let _ = place_of(stored, &probe);
        });
        for (map, symbolic, expected) in [
            (symbolic_values, 0, BuiltinResult::Value(bool_term(false))),
            (symbolic_key, 1, BuiltinResult::NotApplicable),
        ] {
            let made = compared_by(&|| {
                assert_eq!(hook("MAP.in_keys", &[probe.clone(), map.clone()]), expected);
            });
            assert!(
                made <= searched + 1 + symbolic,
                "{made} entries compared, the search compares {searched}, {symbolic} symbolic keys"
            );
        }
    }
}
