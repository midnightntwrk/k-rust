//! `LIST` against `Vec`, `MAP` against `BTreeMap`, and `SET` against `BTreeSet`.
//!
//! Elements are the domain values `i0`..`i4` of one sort and up to three element variables, so
//! that symbolic elements and keys meet concrete ones and each other, and an assignment may make
//! two syntactically different elements equal; a second operand built from the first often
//! replaces an element by a variable bound to the same value. A collection argument may end in
//! (lists: have in its middle) a variable standing for an opaque segment, which the assignment
//! fills.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, Sign};
use num_traits::{Signed, ToPrimitive};

use super::{
    Case, Draw, Env, Shapes, Spec, Val, assert_reached, item, item_sort, list_definition,
    map_definition, run, set_definition, variable, with_shapes,
};
use crate::term::{Sort, Term};

const CASES: u32 = 3000;

fn element(draw: &mut Draw<'_>, env: &mut Env) -> Term {
    if draw.chance(3) {
        let name = format!("E{}", draw.below(3));
        let value = Val::Item(draw.below(5) as u8);
        env.entry(name.clone()).or_insert(value);
        variable(&name, item_sort())
    } else {
        item(draw.below(5) as u8)
    }
}

/// `term`, or sometimes a fresh variable the instance binds to the value `term` denotes: two
/// operands that differ in syntax but not in value, which a hook must not separate.
fn disguise(draw: &mut Draw<'_>, env: &mut Env, term: &Term) -> Term {
    if draw.chance(2) && term.attributes().variables.is_empty() {
        let name = draw.fresh_name("D");
        env.insert(
            name.clone(),
            super::decode(term, &Env::new()).expect("a concrete element"),
        );
        variable(&name, item_sort())
    } else {
        term.clone()
    }
}

fn items(draw: &mut Draw<'_>, most: usize) -> Vec<Val> {
    (0..draw.below(most + 1))
        .map(|_| Val::Item(draw.below(5) as u8))
        .collect()
}

fn list(draw: &mut Draw<'_>, env: &mut Env) -> Term {
    let heads = (0..draw.below(4)).map(|_| element(draw, env)).collect();
    let rest = draw.chance(3).then(|| {
        let name = draw.fresh_name("L");
        env.insert(name.clone(), Val::List(items(draw, 2)));
        let tails = (0..draw.below(3)).map(|_| element(draw, env)).collect();
        let sort = Sort::simple(list_definition().list_sort.clone());
        (variable(&name, sort), tails)
    });
    Term::list(list_definition(), heads, rest)
}

struct MapShape {
    entries: Vec<(Term, Term)>,
    rest: Option<Term>,
}

impl MapShape {
    fn term(&self) -> Term {
        Term::map(map_definition(), self.entries.clone(), self.rest.clone())
    }
}

fn map_shape(draw: &mut Draw<'_>, env: &mut Env) -> MapShape {
    let entries = (0..draw.below(4))
        .map(|_| (element(draw, env), element(draw, env)))
        .collect();
    let rest = draw.chance(2).then(|| {
        let name = draw.fresh_name("M");
        let keys = items(draw, 2);
        let entries = keys
            .into_iter()
            .map(|key| (key, Val::Item(draw.below(5) as u8)))
            .collect();
        env.insert(name.clone(), Val::Map(entries));
        variable(&name, Sort::simple(map_definition().map_sort.clone()))
    });
    MapShape { entries, rest }
}

/// A second map operand: often built from the first one (the same map, some entries dropped or
/// changed, or entries added), so that inclusion, update and concatenation meet shared keys.
fn related_map(draw: &mut Draw<'_>, env: &mut Env, first: &MapShape) -> Term {
    match draw.below(4) {
        0 => {
            let mut entries = first.entries.clone();
            entries.retain(|_| !draw.chance(3));
            for entry in &mut entries {
                if draw.chance(2) {
                    entry.1 = element(draw, env);
                } else {
                    entry.1 = disguise(draw, env, &entry.1);
                }
            }
            if draw.chance(4) {
                entries.push((element(draw, env), element(draw, env)));
            }
            let rest = if draw.chance(4) {
                first.rest.clone()
            } else {
                None
            };
            Term::map(map_definition(), entries, rest)
        }
        1 => first.term(),
        _ => map_shape(draw, env).term(),
    }
}

/// A key to look up: often one of the map's keys, possibly disguised.
fn map_key(draw: &mut Draw<'_>, env: &mut Env, map: &MapShape) -> Term {
    if !map.entries.is_empty() && draw.chance(4) {
        let key = map.entries[draw.below(map.entries.len())].0.clone();
        disguise(draw, env, &key)
    } else {
        element(draw, env)
    }
}

fn set(draw: &mut Draw<'_>, env: &mut Env) -> Term {
    let elements = (0..draw.below(4)).map(|_| element(draw, env)).collect();
    let rest = draw.chance(2).then(|| {
        let name = draw.fresh_name("S");
        let values = items(draw, 2).into_iter().collect();
        env.insert(name.clone(), Val::Set(values));
        variable(&name, Sort::simple(set_definition().list_sort.clone()))
    });
    Term::set(set_definition(), elements, rest)
}

/// A second set operand: often the first one, or a subset or superset of it.
fn related_set(draw: &mut Draw<'_>, env: &mut Env, first: &Term) -> Term {
    if draw.chance(4) {
        return set(draw, env);
    }
    let crate::term::TermKind::Set { elements, rest, .. } = first.kind() else {
        return first.clone();
    };
    let mut elements = elements.to_vec();
    elements.retain(|_| !draw.chance(2));
    for element in &mut elements {
        *element = disguise(draw, env, element);
    }
    if draw.chance(3) {
        elements.push(element(draw, env));
    }
    let rest = if draw.chance(4) { rest.clone() } else { None };
    Term::set(set_definition(), elements, rest)
}

fn index_arguments(draw: &mut Draw<'_>, env: &mut Env, count: usize) -> Vec<Term> {
    (0..count)
        .map(|_| {
            let index = draw.index(4);
            draw.int(index, env)
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------
// LIST

const LIST_HOOKS: [&str; 10] = [
    "LIST.concat",
    "LIST.element",
    "LIST.in",
    "LIST.size",
    "LIST.unit",
    "LIST.get",
    "LIST.make",
    "LIST.range",
    "LIST.update",
    "LIST.updateAll",
];

fn list_case(draw: &mut Draw<'_>) -> Case {
    let hook = draw.pick(&LIST_HOOKS);
    let mut env = Env::new();
    let env = &mut env;
    let arguments = match hook {
        "LIST.concat" => vec![list(draw, env), list(draw, env)],
        "LIST.element" => vec![element(draw, env)],
        "LIST.in" => vec![element(draw, env), list(draw, env)],
        "LIST.size" => vec![list(draw, env)],
        "LIST.unit" => vec![],
        "LIST.get" => {
            let mut arguments = vec![list(draw, env)];
            arguments.extend(index_arguments(draw, env, 1));
            arguments
        }
        "LIST.make" => {
            let length = draw.below(8) as i64 - 2;
            vec![draw.int(length, env), element(draw, env)]
        }
        "LIST.range" => {
            let mut arguments = vec![list(draw, env)];
            arguments.extend(index_arguments(draw, env, 2));
            arguments
        }
        "LIST.update" => {
            let mut arguments = vec![list(draw, env)];
            arguments.extend(index_arguments(draw, env, 1));
            arguments.push(element(draw, env));
            arguments
        }
        "LIST.updateAll" => {
            let mut arguments = vec![list(draw, env)];
            arguments.extend(index_arguments(draw, env, 1));
            arguments.push(list(draw, env));
            arguments
        }
        _ => unreachable!(),
    };
    Case {
        hook,
        arguments,
        env: env.clone(),
    }
}

/// `index` as a position in a sequence of `length` elements, if it is one.
fn position(index: &BigInt, length: usize) -> Option<usize> {
    index.to_usize().filter(|index| *index < length)
}

fn list_model(hook: &str, arguments: &[Val]) -> Spec {
    use Val::{Bool, Int, List};
    match (hook, arguments) {
        ("LIST.concat", [List(left), List(right)]) => {
            Spec::value(List(left.iter().chain(right).cloned().collect()))
        }
        ("LIST.element", [value]) => Spec::value(List(vec![value.clone()])),
        ("LIST.in", [value, List(list)]) => Spec::value(Bool(list.contains(value))),
        ("LIST.size", [List(list)]) => Spec::value(Val::int(list.len())),
        ("LIST.unit", []) => Spec::value(List(Vec::new())),
        // Non-negative indices count from the front, from 0; negative ones from the back, from
        // -1.
        ("LIST.get", [List(list), Int(index)]) => {
            let index = if index.is_negative() {
                (BigInt::from(list.len()) + index).to_usize()
            } else {
                index.to_usize()
            };
            Spec::partial(index.and_then(|index| list.get(index)).cloned())
        }
        ("LIST.make", [Int(length), value]) => Spec::partial(
            length
                .to_usize()
                .map(|length| List(vec![value.clone(); length])),
        ),
        ("LIST.range", [List(list), Int(front), Int(back)]) => {
            let length = BigInt::from(list.len());
            Spec::partial(
                (front.sign() != Sign::Minus
                    && back.sign() != Sign::Minus
                    && front + back <= length)
                    .then(|| {
                        let (front, back) = (front.to_usize().unwrap(), back.to_usize().unwrap());
                        List(list[front..list.len() - back].to_vec())
                    }),
            )
        }
        ("LIST.update", [List(list), Int(index), value]) => {
            Spec::partial(position(index, list.len()).map(|index| {
                let mut list = list.clone();
                list[index] = value.clone();
                List(list)
            }))
        }
        // `index + N > K yields an exception`; a negative index is no position either.
        ("LIST.updateAll", [List(destination), Int(index), List(source)]) => Spec::partial(
            (index.sign() != Sign::Minus
                && index + BigInt::from(source.len()) <= BigInt::from(destination.len()))
            .then(|| {
                let index = index.to_usize().unwrap();
                let mut list = destination.clone();
                list.splice(index..index + source.len(), source.iter().cloned());
                List(list)
            }),
        ),
        _ => panic!("no LIST model for {hook} on {arguments:?}"),
    }
}

#[test]
fn list_hooks_agree_with_a_vec_model() {
    for shapes in [Shapes::builtin(), Shapes::renamed()] {
        with_shapes(shapes, || {
            let tallies = run(CASES, &list_case, &list_model);
            assert_reached(
                &tallies,
                &LIST_HOOKS,
                &[
                    "LIST.concat",
                    "LIST.in",
                    "LIST.get",
                    "LIST.range",
                    "LIST.update",
                    "LIST.size",
                ],
            );
        });
    }
}

// ---------------------------------------------------------------------------------------------
// MAP

const MAP_HOOKS: [&str; 15] = [
    "MAP.element",
    "MAP.unit",
    "MAP.update",
    "MAP.updateAll",
    "MAP.remove",
    "MAP.removeAll",
    "MAP.size",
    "MAP.lookupOrDefault",
    "MAP.in_keys",
    "MAP.keys",
    "MAP.keys_list",
    "MAP.values",
    "MAP.inclusion",
    "MAP.concat",
    "MAP.lookup",
];

fn map_case(draw: &mut Draw<'_>) -> Case {
    let hook = draw.pick(&MAP_HOOKS);
    let mut env = Env::new();
    let env = &mut env;
    let arguments = match hook {
        "MAP.element" => vec![element(draw, env), element(draw, env)],
        "MAP.unit" => vec![],
        "MAP.update" | "MAP.lookupOrDefault" => {
            let map = map_shape(draw, env);
            let key = map_key(draw, env, &map);
            vec![map.term(), key, element(draw, env)]
        }
        "MAP.remove" | "MAP.lookup" => {
            let map = map_shape(draw, env);
            let key = map_key(draw, env, &map);
            vec![map.term(), key]
        }
        "MAP.in_keys" => {
            let map = map_shape(draw, env);
            let key = map_key(draw, env, &map);
            vec![key, map.term()]
        }
        "MAP.removeAll" => vec![map_shape(draw, env).term(), set(draw, env)],
        "MAP.size" | "MAP.keys" | "MAP.keys_list" | "MAP.values" => {
            vec![map_shape(draw, env).term()]
        }
        "MAP.updateAll" | "MAP.inclusion" | "MAP.concat" => {
            let first = map_shape(draw, env);
            let second = related_map(draw, env, &first);
            if draw.chance(4) {
                vec![second, first.term()]
            } else {
                vec![first.term(), second]
            }
        }
        _ => unreachable!(),
    };
    Case {
        hook,
        arguments,
        env: env.clone(),
    }
}

fn map_model(hook: &str, arguments: &[Val]) -> Spec {
    use Val::{Bool, Map, Set};
    match (hook, arguments) {
        ("MAP.element", [key, value]) => {
            Spec::value(Map(BTreeMap::from([(key.clone(), value.clone())])))
        }
        ("MAP.unit", []) => Spec::value(Map(BTreeMap::new())),
        ("MAP.update", [Map(map), key, value]) => {
            let mut map = map.clone();
            map.insert(key.clone(), value.clone());
            Spec::value(Map(map))
        }
        ("MAP.updateAll", [Map(map), Map(updates)]) => {
            let mut map = map.clone();
            map.extend(updates.clone());
            Spec::value(Map(map))
        }
        ("MAP.remove", [Map(map), key]) => {
            let mut map = map.clone();
            map.remove(key);
            Spec::value(Map(map))
        }
        ("MAP.removeAll", [Map(map), Set(keys)]) => {
            let mut map = map.clone();
            map.retain(|key, _| !keys.contains(key));
            Spec::value(Map(map))
        }
        ("MAP.size", [Map(map)]) => Spec::value(Val::int(map.len())),
        ("MAP.lookupOrDefault", [Map(map), key, default]) => {
            Spec::value(map.get(key).unwrap_or(default).clone())
        }
        ("MAP.in_keys", [key, Map(map)]) => Spec::value(Bool(map.contains_key(key))),
        ("MAP.keys", [Map(map)]) => Spec::value(Set(map.keys().cloned().collect())),
        ("MAP.keys_list", [Map(map)]) => Spec::permutation(map.keys().cloned().collect()),
        ("MAP.values", [Map(map)]) => Spec::permutation(map.values().cloned().collect()),
        ("MAP.inclusion", [Map(left), Map(right)]) => Spec::value(Bool(
            left.iter()
                .all(|(key, value)| right.get(key) == Some(value)),
        )),
        // Concatenation is defined only on maps with disjoint keys.
        ("MAP.concat", [Map(left), Map(right)]) => {
            Spec::partial(left.keys().all(|key| !right.contains_key(key)).then(|| {
                Map(left
                    .iter()
                    .chain(right)
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect())
            }))
        }
        ("MAP.lookup", [Map(map), key]) => Spec::partial(map.get(key).cloned()),
        _ => panic!("no MAP model for {hook} on {arguments:?}"),
    }
}

#[test]
fn map_hooks_agree_with_a_btreemap_model() {
    for shapes in [Shapes::builtin(), Shapes::renamed()] {
        with_shapes(shapes, || {
            let tallies = run(CASES, &map_case, &map_model);
            assert_reached(
                &tallies,
                &MAP_HOOKS,
                &[
                    "MAP.element",
                    "MAP.update",
                    "MAP.updateAll",
                    "MAP.remove",
                    "MAP.lookupOrDefault",
                    "MAP.in_keys",
                    "MAP.inclusion",
                    "MAP.concat",
                    "MAP.lookup",
                ],
            );
        });
    }
}

/// `MAP.values` lists the values in the order `MAP.keys_list` lists their keys, so that the two
/// lists pair up into the map's bindings.
#[test]
fn map_values_follow_the_order_of_keys_list() {
    for size in 0..6_u8 {
        for offset in 0..5_u8 {
            let bindings = (0..size)
                .map(|index| {
                    (
                        Val::Item((index * 3 + offset) % 7),
                        Val::Item((index + offset) % 5),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let map = super::encode(&Val::Map(bindings.clone()));
            let project = |hook| {
                let Ok(super::BuiltinResult::Value(list)) =
                    super::evaluate(hook, std::slice::from_ref(&map))
                else {
                    panic!("{hook} does not evaluate a concrete map")
                };
                let Some(Val::List(values)) = super::decode(&list, &Env::new()) else {
                    panic!("{hook} is not a list")
                };
                values
            };
            let pairs = project("MAP.keys_list")
                .into_iter()
                .zip(project("MAP.values"))
                .collect::<BTreeMap<_, _>>();
            assert_eq!(pairs, bindings);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// SET

const SET_HOOKS: [&str; 11] = [
    "SET.concat",
    "SET.element",
    "SET.unit",
    "SET.in",
    "SET.difference",
    "SET.set2list",
    "SET.size",
    "SET.intersection",
    "SET.list2set",
    "SET.inclusion",
    "SET.union",
];

fn set_case(draw: &mut Draw<'_>) -> Case {
    let hook = draw.pick(&SET_HOOKS);
    let mut env = Env::new();
    let env = &mut env;
    let arguments = match hook {
        "SET.element" => vec![element(draw, env)],
        "SET.unit" => vec![],
        "SET.in" => vec![element(draw, env), set(draw, env)],
        "SET.set2list" | "SET.size" => vec![set(draw, env)],
        "SET.list2set" => vec![list(draw, env)],
        "SET.concat" | "SET.difference" | "SET.intersection" | "SET.inclusion" | "SET.union" => {
            let first = set(draw, env);
            let second = related_set(draw, env, &first);
            if draw.chance(4) {
                vec![second, first]
            } else {
                vec![first, second]
            }
        }
        _ => unreachable!(),
    };
    Case {
        hook,
        arguments,
        env: env.clone(),
    }
}

fn set_model(hook: &str, arguments: &[Val]) -> Spec {
    use Val::{Bool, List, Set};
    match (hook, arguments) {
        // Concatenation is the disjoint union: `SetItem(X) SetItem(X)` is `\bottom`.
        ("SET.concat", [Set(left), Set(right)]) => Spec::partial(
            left.is_disjoint(right)
                .then(|| Set(left.union(right).cloned().collect())),
        ),
        ("SET.element", [value]) => Spec::value(Set(BTreeSet::from([value.clone()]))),
        ("SET.unit", []) => Spec::value(Set(BTreeSet::new())),
        ("SET.in", [value, Set(set)]) => Spec::value(Bool(set.contains(value))),
        ("SET.difference", [Set(left), Set(right)]) => {
            Spec::value(Set(left.difference(right).cloned().collect()))
        }
        ("SET.set2list", [Set(set)]) => Spec::permutation(set.iter().cloned().collect()),
        ("SET.size", [Set(set)]) => Spec::value(Val::int(set.len())),
        ("SET.intersection", [Set(left), Set(right)]) => {
            Spec::value(Set(left.intersection(right).cloned().collect()))
        }
        ("SET.list2set", [List(list)]) => Spec::value(Set(list.iter().cloned().collect())),
        ("SET.inclusion", [Set(left), Set(right)]) => Spec::value(Bool(left.is_subset(right))),
        ("SET.union", [Set(left), Set(right)]) => {
            Spec::value(Set(left.union(right).cloned().collect()))
        }
        _ => panic!("no SET model for {hook} on {arguments:?}"),
    }
}

#[test]
fn set_hooks_agree_with_a_btreeset_model() {
    for shapes in [Shapes::builtin(), Shapes::renamed()] {
        with_shapes(shapes, || {
            let tallies = run(CASES, &set_case, &set_model);
            assert_reached(
                &tallies,
                &SET_HOOKS,
                &["SET.concat", "SET.element", "SET.in"],
            );
        });
    }
}
