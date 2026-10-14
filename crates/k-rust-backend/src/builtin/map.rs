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
//!   only, `O(s log n)`; a key that is not constructor-like with every entry, `O(n)`. A key
//!   declared at a sort above the key sort that is no injected key is compared with each key
//!   injected into its sort, `O(n)` (`collection_item`).
//! - `update`, `remove`: one search and one path copy, `O(log n)`.
//! - `updateAll`, `removeAll`: one search and one path copy per item of the second argument,
//!   `O(m log n)`; `inclusion`: one search in the right map per entry of the left, `O(m log n)`.
//! - `difference`: one search in the right map per entry of the left, and one path copy per
//!   binding removed, `O(n log m + r log n)` for `r` removed; a key the search does not find is
//!   decided absent by `absent`, as for `lookup`.
//! - `concat`: the union of the two trees, `O(m log(n/m + 1))`, a repeated key read from the
//!   union's summary.
//! - `keys`, `keys_list`, `values`: `O(n)`, the size of the result.
//! - `choice`: the first stored entry, one descent of the tree, `O(log n)`.

use std::borrow::Cow;

use num_bigint::BigInt;

use super::{
    BuiltinError, BuiltinResult, HookResult, ResultCollection, UnsupportedHookReason, bool_term,
    collection_item::{self, Operand},
    expect_arity, expect_sort, int_term,
    result_collection::MapResult,
    values_differ,
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
        "MAP.difference" => difference(arguments, sorts, result),
        "MAP.concat" => return concat(arguments, result),
        "MAP.lookup" => return lookup(arguments, sorts),
        "MAP.choice" => return choice(arguments),
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

/// `choice(M)`: some key of `M`, the same key for the same map (`domains.md`), from a `function`
/// that is not `total`.
///
/// The empty map has no key, so the application is undefined. A map of one binding `K |-> V` has
/// the one key `K`, and every function the declaration admits gives it, whether or not `K` is
/// constructor-like. A map with an opaque rest beside at most one binding may be a map of one
/// binding under an instance, so the application waits for one.
///
/// A map of two or more bindings has two or more keys wherever it is defined (map concatenation
/// binds each key once), and which of them the hook gives is not a consequence of the definition.
/// k-rust's choice is the key `keys_list` lists first, the first of the map's stored entries
/// (`ordered_entries`), so the two hooks agree. With every key constructor-like and no rest, the
/// stored order is the order of the keys' values (domain values are canonical), so the choice is
/// a function of the map, as the `function` declaration requires. Only an execution takes it:
/// elsewhere the application is a defined value left unevaluated (`super::implementation_chosen`).
/// A key that is not constructor-like, or an opaque rest, may put another key first in an
/// instance, so the application waits. The first entry is one descent of the tree, `O(log n)`.
fn choice(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("MAP.choice", arguments, 1)?;
    let TermKind::Map { entries, rest, .. } = arguments[0].kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(match (entries.len(), rest) {
        (0, None) => BuiltinResult::Bottom,
        (1, None) => {
            let (key, _) = entries.get(0).expect("a one-binding map's entry");
            BuiltinResult::Value(key.clone())
        }
        _ => match ordered_entries(&arguments[0]).and_then(|(_, entries)| entries.first()) {
            Some((key, _)) => BuiltinResult::Value(key.clone()),
            None => BuiltinResult::NotApplicable,
        },
    })
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

/// What a map binds to a key operand read as a key of the map (`collection_item`).
enum Binding<'a> {
    /// The value bound to the key.
    Bound(&'a Term),
    /// The map binds no such key.
    Unbound,
    /// Not decided: a symbolic key or an opaque rest may bind it, or no injection is known to
    /// relate the key operand to the map's keys.
    Undecided,
}

/// The binding of `key` in the map whose `definition`, `entries` and `rest` are given: the key is
/// read as a key of the map's key sort, searched among the entries, and decided absent by
/// `absent` (`absent_above` for a key of a wider sort that is no injected key).
fn binding<'a>(
    sorts: Option<&SortGraph>,
    key: &Term,
    definition: &MapDefinition,
    entries: &'a Items<(Term, Term)>,
    rest: &Option<Term>,
) -> Binding<'a> {
    let key = match collection_item::read(sorts, key, &definition.key_sort) {
        Operand::Element(key) => key,
        Operand::Wider { item, sort } => {
            return if rest.is_none()
                && collection_item::absent_above(
                    sorts,
                    item,
                    &sort,
                    &definition.key_sort,
                    entries.iter().map(|(key, _)| key),
                ) {
                Binding::Unbound
            } else {
                Binding::Undecided
            };
        }
        Operand::Unrelated => return Binding::Undecided,
    };
    if let Some(index) = bound_at(entries, &*key) {
        let (_, value) = entries.get(index).expect("a bound key's entry");
        return Binding::Bound(value);
    }
    if absent(sorts, &key, entries, rest) {
        Binding::Unbound
    } else {
        Binding::Undecided
    }
}

fn lookup(arguments: &[Term], sorts: Option<&SortGraph>) -> HookResult<BuiltinResult> {
    expect_arity("MAP.lookup", arguments, 2)?;
    let [map, key] = arguments else {
        unreachable!()
    };
    let TermKind::Map {
        definition,
        entries,
        rest,
    } = map.kind()
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(match binding(sorts, key, definition, entries, rest) {
        Binding::Bound(value) => BuiltinResult::Value(value.clone()),
        Binding::Unbound => BuiltinResult::Bottom,
        Binding::Undecided => BuiltinResult::NotApplicable,
    })
}

fn lookup_or_default(arguments: &[Term], sorts: Option<&SortGraph>) -> HookResult<Option<Term>> {
    expect_arity("MAP.lookupOrDefault", arguments, 3)?;
    let [map, key, default] = arguments else {
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
    Ok(match binding(sorts, key, definition, entries, rest) {
        Binding::Bound(value) => Some(value.clone()),
        Binding::Unbound => Some(default.clone()),
        Binding::Undecided => None,
    })
}

fn in_keys(arguments: &[Term], sorts: Option<&SortGraph>) -> HookResult<Option<Term>> {
    expect_arity("MAP.in_keys", arguments, 2)?;
    let [key, map] = arguments else {
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
    Ok(match binding(sorts, key, definition, entries, rest) {
        Binding::Bound(_) => Some(bool_term(true)),
        Binding::Unbound => Some(bool_term(false)),
        Binding::Undecided => None,
    })
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

/// Whether `keys_list` and `values` of `arguments` list two or more bindings, in an order the
/// definition leaves open (`super::implementation_chosen`).
pub(super) fn lists_several_items(arguments: &[Term]) -> bool {
    matches!(arguments, [map] if ordered_entries(map).is_some_and(|(_, entries)| entries.len() >= 2))
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

/// `M1 -Map M2`: the bindings of `M1` that `M2` does not hold with the same value
/// (`domains.md`: only keys whose value is the same in both maps are removed). The hook is
/// `total`, so an application whose value this does not decide is left unevaluated.
///
/// Each binding `K |-> V` of a closed `M1` is decided on its own. Where `M2` binds `K`
/// syntactically, to `W`, it binds that key and no other to `W` (a map binds each key once), so
/// the binding is removed when `V` and `W` are the same term and kept when they are different
/// values (`values_differ`: two different constructor-like terms, or apart terms); otherwise the
/// two values may or may not be equal. Where `M2` does not bind `K` syntactically, the binding is
/// kept when `K` is no key of `M2` (`absent`); otherwise a key of `M2` that is not
/// constructor-like, or `M2`'s rest, may be `K`. One binding left undecided leaves the whole
/// application undecided.
///
/// Three cases hold whatever the bindings: a map without the bindings of the empty map is
/// itself, the empty map without any bindings is empty, and a map without its own bindings is
/// empty, rests included, because equal terms denote equal maps. A map with an opaque rest is
/// decided by those cases only: the rest may hold any binding of `M2`.
fn difference(
    arguments: &[Term],
    sorts: Option<&SortGraph>,
    result: ResultCollection<'_>,
) -> HookResult<Option<Term>> {
    expect_arity("MAP.difference", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    let closed_empty = |map: &Term| matches!(map.kind(), TermKind::Map { entries, rest: None, .. } if entries.is_empty());
    let source = match (left.kind(), right.kind()) {
        (
            TermKind::Map { definition, .. },
            TermKind::Map {
                definition: right_definition,
                ..
            },
        ) => {
            if definition != right_definition {
                return Ok(None);
            }
            Some(definition)
        }
        // A whole map without a map of its sort: the operand that is no map term (a map
        // variable, an unevaluated function) must be of the map term's sort.
        (TermKind::Map { definition, .. }, _) => {
            (right.sort() == map_sort(definition)).then_some(definition)
        }
        (_, TermKind::Map { definition, .. }) => {
            (left.sort() == map_sort(definition)).then_some(definition)
        }
        _ => None,
    };
    if left == right || (source.is_some() && closed_empty(left)) {
        return Ok(result
            .map(source)
            .and_then(|into| into.build(Vec::new(), None)));
    }
    let Some(definition) = source else {
        return Ok(None);
    };
    if closed_empty(right) {
        return Ok(result
            .map(Some(definition))
            .and_then(|into| into.adopt(left)));
    }
    let (
        TermKind::Map {
            entries,
            rest: None,
            ..
        },
        TermKind::Map {
            entries: right_entries,
            rest: right_rest,
            ..
        },
    ) = (left.kind(), right.kind())
    else {
        return Ok(None);
    };
    let Some(into) = result.map(Some(definition)) else {
        return Ok(None);
    };
    let mut removed = Vec::new();
    for (index, (key, value)) in entries.iter().enumerate() {
        let remove = match bound_at(right_entries, key).and_then(|at| right_entries.get(at)) {
            Some((_, other)) if value == other => true,
            Some((_, other)) if values_differ(sorts, value, other) => false,
            Some(_) => return Ok(None),
            None if absent(sorts, key, right_entries, right_rest) => false,
            None => return Ok(None),
        };
        if remove {
            removed.push(index);
        }
    }
    if removed.is_empty() {
        return Ok(into.adopt(left));
    }
    // Removing from the last place keeps the places of the bindings before it.
    let kept = removed
        .iter()
        .rev()
        .fold(entries.clone(), |kept, &index| kept.remove_at(index).0);
    Ok(into.build_from(Cow::Owned(kept), definition, None))
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
        Term::raw_domain_value(Sort::simple("SortKey"), value)
    }

    fn value(value: &str) -> Term {
        Term::raw_domain_value(Sort::simple("SortValue"), value)
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

    fn choice_of(map: Term) -> BuiltinResult {
        super::super::evaluate_hook("MAP.choice", &[map])
            .unwrap()
            .unwrap()
    }

    /// The empty map has no key, and `choice` is partial: the application is undefined.
    #[test]
    fn choice_of_the_empty_collection_is_bottom() {
        assert_eq!(
            choice_of(Term::map(definition("SortMap"), Vec::new(), None)),
            BuiltinResult::Bottom
        );
    }

    /// A map of one binding has one key, which every admitted choice gives, also when it is a
    /// variable; with a rest beside it the map may hold other keys, so the application waits.
    #[test]
    fn choice_of_a_one_item_collection_is_its_item_even_symbolic() {
        assert_eq!(
            choice_of(Term::map(
                definition("SortMap"),
                vec![(key("5"), value("50"))],
                None
            )),
            BuiltinResult::Value(key("5"))
        );
        let x = Term::variable(Variable::new("X", Sort::simple("SortKey")));
        assert_eq!(
            choice_of(Term::map(
                definition("SortMap"),
                vec![(x.clone(), value("1"))],
                None
            )),
            BuiltinResult::Value(x.clone())
        );
        let rest = Term::variable(Variable::new("R", Sort::simple("SortMap")));
        assert_eq!(
            choice_of(Term::map(
                definition("SortMap"),
                vec![(x, value("1"))],
                Some(rest.clone())
            )),
            BuiltinResult::NotApplicable
        );
        assert_eq!(choice_of(rest), BuiltinResult::NotApplicable);
    }

    /// The first key `keys_list` lists of `map`, which lists in the map's stored order.
    fn first_listed_key(map: &Term) -> Term {
        let Ok(Some(list)) = keys_list(std::slice::from_ref(map), into(&key_list())) else {
            panic!("keys_list of {map:?} is not evaluated");
        };
        let TermKind::List { heads, .. } = list.kind() else {
            panic!("keys_list of {map:?} is no list: {list:?}");
        };
        heads.first().expect("a key").clone()
    }

    /// `choice` of a closed map of two or more constructor-like keys is the key `keys_list`
    /// lists first, k-rust's documented order (the decimal text order for `Int` keys), so the
    /// two hooks share one choice. The stored order is a function of the map's value: the same
    /// map built by concatenations in either order, or with two spellings of one `Float` key,
    /// gives the same key. A symbolic key beside others, or an opaque rest, may put another key
    /// first in an instance, so the application waits.
    #[test]
    fn choice_is_the_first_key_keys_list_lists() {
        let map = |entries: &[(Term, &str)]| {
            Term::map(
                definition("SortMap"),
                entries
                    .iter()
                    .map(|(key, to)| (key.clone(), value(to)))
                    .collect(),
                None,
            )
        };
        let int = |value: i64| Term::int(value);
        let three = map(&[(int(3), "30"), (int(1), "10"), (int(2), "20")]);
        assert_eq!(choice_of(three.clone()), BuiltinResult::Value(int(1)));
        assert_eq!(first_listed_key(&three), int(1));
        let text_order = map(&[(int(10), "a"), (int(2), "b")]);
        assert_eq!(choice_of(text_order.clone()), BuiltinResult::Value(int(10)));
        assert_eq!(first_listed_key(&text_order), int(10));
        let concatenated = |first: &Term, second: &Term| {
            let BuiltinResult::Value(map) = hook("MAP.concat", &[first.clone(), second.clone()])
            else {
                panic!("the concatenation is evaluated");
            };
            map
        };
        let (ten, two) = (map(&[(int(10), "a")]), map(&[(int(2), "b")]));
        assert_eq!(
            choice_of(concatenated(&ten, &two)),
            choice_of(concatenated(&two, &ten))
        );
        let float = |text: &str| {
            Term::domain_value_of(
                crate::term::DomainKind::Float,
                Sort::simple("SortFloat"),
                text,
            )
        };
        let written = map(&[(float("2.0"), "a"), (float("1.5"), "b")]);
        let respelled = map(&[(float("0.2e1"), "a"), (float("1.5"), "b")]);
        assert_eq!(choice_of(written.clone()), choice_of(respelled));
        assert_eq!(
            choice_of(written.clone()),
            BuiltinResult::Value(first_listed_key(&written))
        );
        let k = Term::variable(Variable::new("K", Sort::simple("SortKey")));
        let rest = Term::variable(Variable::new("R", Sort::simple("SortMap")));
        for undecided in [
            map(&[(int(1), "10"), (k, "20")]),
            Term::map(
                definition("SortMap"),
                vec![(int(1), value("10")), (int(2), value("20"))],
                Some(rest),
            ),
        ] {
            assert_eq!(
                choice_of(undecided.clone()),
                BuiltinResult::NotApplicable,
                "{undecided:?}"
            );
        }
    }

    fn bindings(definition: &Arc<MapDefinition>, entries: &[(&str, &str)]) -> Term {
        Term::map(
            definition.clone(),
            entries
                .iter()
                .map(|(bound, to)| (key(bound), value(to)))
                .collect(),
            None,
        )
    }

    /// `-Map` removes a binding only where the other map binds its key to the same value: a key
    /// the other map binds to another value stays, as does a key it does not bind.
    #[test]
    fn difference_removes_only_bindings_held_with_the_same_value() {
        let definition = definition("SortMap");
        let left = bindings(&definition, &[("1", "10"), ("2", "20"), ("3", "30")]);
        let right = bindings(&definition, &[("1", "10"), ("2", "99")]);
        assert_eq!(
            hook("MAP.difference", &[left.clone(), right]),
            BuiltinResult::Value(bindings(&definition, &[("2", "20"), ("3", "30")]))
        );
        let empty = bindings(&definition, &[]);
        assert_eq!(
            hook("MAP.difference", &[left.clone(), empty.clone()]),
            BuiltinResult::Value(left.clone())
        );
        assert_eq!(
            hook("MAP.difference", &[empty.clone(), left]),
            BuiltinResult::Value(empty)
        );
        // A key both bind to one symbolic value, or to two values that differ, is decided too.
        let k = Term::variable(Variable::new("K", Sort::simple("SortKey")));
        let symbolic = Term::map(definition.clone(), vec![(k.clone(), value("10"))], None);
        let other = Term::map(
            definition.clone(),
            vec![(k.clone(), value("20")), (key("1"), value("10"))],
            None,
        );
        assert_eq!(
            difference(&[symbolic.clone(), other], None, undeclared()),
            Ok(Some(symbolic.clone()))
        );
        let same = Term::map(
            definition.clone(),
            vec![(k, value("10")), (key("1"), value("10"))],
            None,
        );
        assert_eq!(
            difference(&[symbolic, same], None, undeclared()),
            Ok(Some(bindings(&definition, &[])))
        );
    }

    /// A binding whose value may or may not be the other map's value of its key, or whose key may
    /// or may not be a key of the other map, leaves the application unevaluated: the hook is
    /// `total`, so its value is then left to the simplifier.
    #[test]
    fn difference_with_an_undecided_value_or_key_is_not_evaluated() {
        let foreign = Term::map(definition("SortOther"), vec![(key("1"), value("10"))], None);
        let definition = definition("SortMap");
        let v = Term::variable(Variable::new("V", Sort::simple("SortValue")));
        let k = Term::variable(Variable::new("K", Sort::simple("SortKey")));
        let rest = Term::variable(Variable::new("R", Sort::simple("SortMap")));
        let symbolic_value = Term::map(definition.clone(), vec![(key("1"), v)], None);
        let symbolic_key = Term::map(definition.clone(), vec![(k, value("10"))], None);
        let opaque = Term::map(
            definition.clone(),
            vec![(key("2"), value("20"))],
            Some(rest.clone()),
        );
        let one = bindings(&definition, &[("1", "10")]);
        for (left, right) in [
            (symbolic_value, one.clone()),
            (one.clone(), symbolic_key),
            (one.clone(), opaque.clone()),
            (opaque, one.clone()),
            (rest, one),
        ] {
            assert_eq!(
                hook("MAP.difference", &[left.clone(), right.clone()]),
                BuiltinResult::NotApplicable,
                "{left:?} -Map {right:?}"
            );
        }
        // Maps of two collections are not compared.
        assert_eq!(
            hook(
                "MAP.difference",
                &[bindings(&definition, &[("1", "10")]), foreign]
            ),
            BuiltinResult::NotApplicable
        );
    }

    /// Equal terms denote equal maps, so a map without its own bindings is empty, whatever its
    /// rest holds and also when it is no more than a map variable.
    #[test]
    fn difference_of_a_map_with_itself_is_empty() {
        let definition = definition("SortMap");
        let rest = Term::variable(Variable::new("R", Sort::simple("SortMap")));
        let v = Term::variable(Variable::new("V", Sort::simple("SortValue")));
        let map = Term::map(
            definition.clone(),
            vec![(key("1"), v), (key("2"), value("20"))],
            Some(rest.clone()),
        );
        let empty = bindings(&definition, &[]);
        assert_eq!(
            hook("MAP.difference", &[map.clone(), map]),
            BuiltinResult::Value(empty.clone())
        );
        let collection = CollectionMetadata::Map(definition);
        assert_eq!(
            difference(&[rest.clone(), rest], None, into(&collection)),
            Ok(Some(empty))
        );
    }

    /// Maps of `SortFloat`, machine-integer and `SortMyInt` values and keys, whose sorts this
    /// definition hooks `FLOAT.Float`, `MINT.MInt` and `INT.Int`, with a `-Map` symbol each.
    const SPELLINGS: &str = r#"[]
module MAIN
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
  hooked-sort SortMInt{S} [hook{}("MINT.MInt"), hasDomainValues{}()]
  sort Sort8{} []
  hooked-sort SortMyInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortFloatMap{}
    [hook{}("MAP.Map"), unit{}(dotFloatMap{}()), element{}(floatItem{}()),
     concat{}(floatConcat{}())]
  hooked-symbol dotFloatMap{}() : SortFloatMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol floatItem{}(SortInt{}, SortFloat{}) : SortFloatMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol floatConcat{}(SortFloatMap{}, SortFloatMap{}) : SortFloatMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
  hooked-symbol floatDifference{}(SortFloatMap{}, SortFloatMap{}) : SortFloatMap{}
    [function{}(), total{}(), hook{}("MAP.difference")]
  hooked-sort SortWordMap{}
    [hook{}("MAP.Map"), unit{}(dotWordMap{}()), element{}(wordItem{}()),
     concat{}(wordConcat{}())]
  hooked-symbol dotWordMap{}() : SortWordMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol wordItem{}(SortInt{}, SortMInt{Sort8{}}) : SortWordMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol wordConcat{}(SortWordMap{}, SortWordMap{}) : SortWordMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
  hooked-symbol wordDifference{}(SortWordMap{}, SortWordMap{}) : SortWordMap{}
    [function{}(), total{}(), hook{}("MAP.difference")]
  hooked-sort SortMyIntMap{}
    [hook{}("MAP.Map"), unit{}(dotMyIntMap{}()), element{}(myIntItem{}()),
     concat{}(myIntConcat{}())]
  hooked-symbol dotMyIntMap{}() : SortMyIntMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol myIntItem{}(SortMyInt{}, SortMyInt{}) : SortMyIntMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol myIntConcat{}(SortMyIntMap{}, SortMyIntMap{}) : SortMyIntMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
  hooked-symbol myIntDifference{}(SortMyIntMap{}, SortMyIntMap{}) : SortMyIntMap{}
    [function{}(), total{}(), hook{}("MAP.difference")]
endmodule []"#;

    /// Values and keys of a sort carrying a builtin hook are compared as the values they denote,
    /// not as written: the definition builds every domain value in its kind's canonical text, so
    /// two spellings of one value are one term. Each case is evaluated in the definition, from
    /// its KORE, and once with a binding the other map does not hold, so that the bindings are
    /// compared one by one rather than as two equal maps.
    #[test]
    fn difference_compares_builtin_values_not_spellings() {
        use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

        let syntax = parse_definition(SPELLINGS).expect("the definition parses");
        let definition = crate::definition::BackendDefinition::internalize(&syntax, "MAIN")
            .expect("the definition loads");
        let term = |pattern: &str| {
            definition
                .internalize_term(&parse_pattern(pattern).expect("the pattern parses"), &[])
                .unwrap_or_else(|error| panic!("{pattern}: {error}"))
        };
        let int = |text: &str| format!(r#"\dv{{SortInt{{}}}}("{text}")"#);
        let float = |text: &str| format!(r#"\dv{{SortFloat{{}}}}("{text}")"#);
        let word = |text: &str| format!(r#"\dv{{SortMInt{{Sort8{{}}}}}}("{text}")"#);
        let my = |text: &str| format!(r#"\dv{{SortMyInt{{}}}}("{text}")"#);
        // (symbol prefix, key, value in the left map, value in the right map, key in the right
        // map, an extra binding of the left map's sorts that the right map does not hold)
        let cases = [
            (
                "float",
                int("1"),
                float("2.0"),
                float("0.2e1"),
                int("1"),
                (int("2"), float("3.0")),
            ),
            (
                "float",
                int("1"),
                float("1.0p113x15"),
                float("1.00p113x15"),
                int("1"),
                (int("2"), float("3.0p113x15")),
            ),
            (
                "word",
                int("1"),
                word("255p8"),
                word("-1p8"),
                int("1"),
                (int("2"), word("3p8")),
            ),
            (
                "myInt",
                my("1"),
                my("07"),
                my("7"),
                my("1"),
                (my("2"), my("3")),
            ),
            (
                "myInt",
                my("07"),
                my("1"),
                my("1"),
                my("7"),
                (my("8"), my("3")),
            ),
        ];
        for (prefix, key, left_value, right_value, right_key, (extra_key, extra_value)) in cases {
            let item = |key: &str, value: &str| format!("{prefix}Item{{}}({key}, {value})");
            let right = item(&right_key, &right_value);
            let empty = term(&format!("dot{}Map{{}}()", capitalized(prefix)));
            let extra = term(&item(&extra_key, &extra_value));
            for (left, expected) in [
                (item(&key, &left_value), empty),
                (
                    format!(
                        "{prefix}Concat{{}}({}, {})",
                        item(&key, &left_value),
                        item(&extra_key, &extra_value)
                    ),
                    extra,
                ),
            ] {
                let application = format!("{prefix}Difference{{}}({left}, {right})");
                let result = super::super::evaluate_in_definition(&term(&application), &definition)
                    .expect("the evaluation does not stop")
                    .expect("the evaluation does not fail");
                assert_eq!(result, BuiltinResult::Value(expected), "{application}");
            }
        }
        // The control: different values stay different.
        let kept = term(&format!("floatItem{{}}({}, {})", int("1"), float("2.0")));
        let application = format!(
            "floatDifference{{}}(floatItem{{}}({}, {}), floatItem{{}}({}, {}))",
            int("1"),
            float("2.0"),
            int("1"),
            float("2.5")
        );
        assert_eq!(
            super::super::evaluate_in_definition(&term(&application), &definition)
                .expect("the evaluation does not stop")
                .expect("the evaluation does not fail"),
            BuiltinResult::Value(kept)
        );
    }

    fn capitalized(prefix: &str) -> String {
        let mut characters = prefix.chars();
        characters
            .next()
            .map(|first| first.to_ascii_uppercase().to_string() + characters.as_str())
            .unwrap_or_default()
    }
}
