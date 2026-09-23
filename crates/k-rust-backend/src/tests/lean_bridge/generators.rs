//! Terms built only through the public constructors of `crate::term`, so that every generated
//! value is one the constructors can produce: maps and sets sorted and deduplicated, collection
//! rests flattened, injections of injections collapsed, `Int` values canonicalized.
//!
//! The alphabets are small, so that repeated symbols, k cells at several depths and macros in
//! every position are frequent, and they vary every field the term model keeps: each symbol
//! attribute the walks read, the fields the model folds into `Sym.other`, sort arguments,
//! variable sorts, two definitions per collection kind, and domain values that are not UTF-8.

use std::sync::Arc;

use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};
use proptest::prelude::*;

use crate::term::{
    CollectionSymbols, FunctionType, ListDefinition, MapDefinition, Name, Sort, Symbol, SymbolType,
    Term, Variable,
};

fn sort() -> impl Strategy<Value = Sort> {
    prop_oneof![
        Just(Sort::builtin(BuiltinSort::Int)),
        Just(Sort::simple("SortKItem")),
        Just(Sort::application(
            "SortList",
            vec![Sort::simple("SortKItem")]
        )),
        Just(Sort::Variable("S".into())),
    ]
}

/// A symbol: the k cell (a name comparison, term.rs:176-178) or a plain name, with every
/// attribute the walks read varied independently, and two values of the fields the model folds
/// into `other`.
fn symbol() -> impl Strategy<Value = Arc<Symbol>> {
    (
        prop_oneof![
            3 => Just(WellKnownSymbol::KCell.as_str()),
            4 => prop_oneof![Just("LblA"), Just("LblB"), Just("kseq")],
        ],
        prop_oneof![
            Just(SymbolType::Constructor),
            Just(SymbolType::Function(FunctionType::Partial)),
            Just(SymbolType::Function(FunctionType::Total)),
        ],
        prop::bool::weighted(0.2),
        any::<(bool, bool, bool, bool)>(),
    )
        .prop_map(
            |(
                name,
                symbol_type,
                macro_or_alias,
                (anywhere, declared_function, injective, other),
            )| {
                let mut symbol = Symbol::constructor(name, Vec::new(), Sort::simple("SortKItem"));
                symbol.attributes.symbol_type = symbol_type;
                symbol.attributes.macro_or_alias = macro_or_alias;
                symbol.attributes.anywhere = anywhere;
                symbol.attributes.declared_function = declared_function;
                symbol.attributes.injective = injective;
                if other {
                    symbol.sort_variables = vec!["S".into()];
                    symbol.attributes.hook = Some("INT.add".into());
                }
                Arc::new(symbol)
            },
        )
}

fn collection_symbols(prefix: &str) -> CollectionSymbols {
    CollectionSymbols {
        unit: format!("{prefix}unit").into(),
        element: format!("{prefix}element").into(),
        concat: format!("{prefix}concat").into(),
    }
}

/// Two definitions per collection kind, which differ only in one sort.
fn element_sort(second: bool) -> Name {
    if second { "SortInt" } else { "SortKItem" }.into()
}

fn map_definition(second: bool) -> Arc<MapDefinition> {
    Arc::new(MapDefinition {
        symbols: collection_symbols("Map"),
        key_sort: element_sort(second),
        value_sort: "SortKItem".into(),
        map_sort: "SortMap".into(),
    })
}

fn list_definition(prefix: &str, second: bool) -> Arc<ListDefinition> {
    Arc::new(ListDefinition {
        symbols: collection_symbols(prefix),
        element_sort: element_sort(second),
        list_sort: format!("Sort{prefix}").into(),
    })
}

fn leaf() -> impl Strategy<Value = Term> {
    prop_oneof![
        (
            sort(),
            prop_oneof![
                Just(b"0".to_vec()),
                Just(b"007".to_vec()),
                Just(b"true".to_vec()),
                Just(vec![0xff, 0x00]),
            ]
        )
            .prop_map(|(sort, value)| Term::domain_value(sort, value)),
        (prop_oneof![Just("X"), Just("Y")], any::<bool>(), sort()).prop_map(
            |(name, element, sort)| Term::variable(if element {
                Variable::new(name, sort)
            } else {
                Variable::set(name, sort)
            })
        ),
        (symbol(), prop::collection::vec(sort(), 0..2))
            .prop_map(|(symbol, sorts)| Term::application(symbol, sorts, Vec::new())),
    ]
}

pub(in crate::tests) fn term() -> impl Strategy<Value = Term> {
    terms(false)
}

/// Like `term`, but two map keys or set elements in three are drawn from `collection_key`, so
/// that maps and sets whose keys share one header (the `ceil_free` class of term.rs), keys with
/// different headers, and equal keys under different values are all frequent.
pub(in crate::tests) fn term_with_ground_keys() -> impl Strategy<Value = Term> {
    terms(true)
}

fn domain_value() -> impl Strategy<Value = Term> {
    (
        prop_oneof![
            Just(Sort::builtin(BuiltinSort::Int)),
            Just(Sort::simple("SortKItem"))
        ],
        prop_oneof![Just("0"), Just("007"), Just("1")],
    )
        .prop_map(|(sort, value)| Term::domain_value(sort, value))
}

/// A domain value, or an injection of one with two sources and two targets.
fn collection_key() -> impl Strategy<Value = Term> {
    let sort = || {
        prop_oneof![
            Just(Sort::builtin(BuiltinSort::Int)),
            Just(Sort::simple("SortKItem"))
        ]
    };
    prop_oneof![
        domain_value(),
        (sort(), sort(), domain_value())
            .prop_map(|(source, target, term)| Term::injection(source, target, term)),
    ]
}

fn terms(keys: bool) -> BoxedStrategy<Term> {
    leaf()
        .prop_recursive(6, 96, 4, move |inner| {
            let key = if keys {
                prop_oneof![2 => collection_key(), 1 => inner.clone()].boxed()
            } else {
                inner.clone().boxed()
            };
            prop_oneof![
                4 => (symbol(), prop::collection::vec(sort(), 0..2), prop::collection::vec(inner.clone(), 0..4))
                    .prop_map(|(symbol, sorts, arguments)| Term::application(symbol, sorts, arguments)),
                1 => (inner.clone(), inner.clone()).prop_map(|(left, right)| Term::and(left, right)),
                1 => (sort(), sort(), inner.clone())
                    .prop_map(|(source, target, term)| Term::injection(source, target, term)),
                1 => (
                    any::<bool>(),
                    prop::collection::vec((key.clone(), inner.clone()), 0..4),
                    prop::option::of(inner.clone()),
                )
                    .prop_map(|(second, entries, rest)| Term::map(map_definition(second), entries, rest)),
                1 => (
                    any::<bool>(),
                    prop::collection::vec(inner.clone(), 0..4),
                    prop::option::of((inner.clone(), prop::collection::vec(inner.clone(), 0..3))),
                )
                    .prop_map(|(second, heads, rest)| {
                        Term::list(list_definition("List", second), heads, rest)
                    }),
                1 => (
                    any::<bool>(),
                    prop::collection::vec(key, 0..4),
                    prop::option::of(inner),
                )
                    .prop_map(|(second, elements, rest)| {
                        Term::set(list_definition("Set", second), elements, rest)
                    }),
            ]
        })
        .boxed()
}
