//! Terms built only through the public constructors of `crate::term`, so that every generated
//! value is one the constructors can produce: maps and sets sorted (a repeated key or element
//! is kept), collection rests flattened, injections of injections collapsed, `Int` values
//! canonicalized.
//!
//! The alphabets are small, so that repeated symbols, k cells at several depths and macros in
//! every position are frequent, and they vary every field the term model keeps: each symbol
//! attribute the walks read, the fields the model folds into `Sym.other`, sort arguments,
//! variable sorts, two definitions per collection kind, and domain values that are not UTF-8.

use std::sync::Arc;

use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};
use proptest::prelude::*;

use crate::term::{
    CollectionSymbols, FunctionType, ListDefinition, MapDefinition, Sort, Symbol, SymbolAttributes,
    SymbolType, Term, TermKind, Variable,
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
                symbol.attributes = SymbolAttributes::constructor()
                    .with_anywhere(anywhere)
                    .with_declared_function(declared_function)
                    .with_injective(injective);
                symbol.attributes.symbol_type = symbol_type;
                symbol.attributes.macro_or_alias = macro_or_alias;
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
fn element_sort(second: bool) -> Sort {
    Sort::simple(if second { "SortInt" } else { "SortKItem" })
}

fn map_definition(second: bool) -> Arc<MapDefinition> {
    Arc::new(MapDefinition {
        symbols: collection_symbols("Map"),
        key_sort: element_sort(second),
        value_sort: Sort::simple("SortKItem"),
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

pub(crate) fn term() -> impl Strategy<Value = Term> {
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

/// The field a one-edit neighbour changes (see [`one_edit_neighbours`]).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::tests) enum Edit {
    /// A collection's rest added (a variable of the collection's sort) or removed.
    Rest,
    /// A collection's definition, swapped for the other definition of its kind (its key or
    /// element sort changed).
    Definition,
    /// A sort: of a domain value, a variable, an injection's source or target, or an
    /// application's first sort argument (one added when it has none; the generators give an
    /// application at most one).
    Sort,
    /// A variable's name.
    Name,
    /// An application's symbol, renamed.
    Symbol,
    /// A domain value's text.
    Value,
}

impl Edit {
    pub(in crate::tests) const ALL: [Self; 6] = [
        Self::Rest,
        Self::Definition,
        Self::Sort,
        Self::Name,
        Self::Symbol,
        Self::Value,
    ];
}

/// A sort other than `sort`.
fn other_sort(sort: &Sort) -> Sort {
    if *sort == Sort::builtin(BuiltinSort::Int) {
        Sort::simple("SortKItem")
    } else {
        Sort::builtin(BuiltinSort::Int)
    }
}

/// The element sort of the other definition of a collection kind (see [`element_sort`]).
fn other_element_sort(sort: &Sort) -> Sort {
    element_sort(*sort != element_sort(true))
}

/// The edits of the node at the root of `term` itself, its children kept.
#[allow(
    clippy::too_many_lines,
    reason = "one arm per node kind, each listing the fields it edits"
)]
fn root_edits(term: &Term) -> Vec<(Edit, Term)> {
    let rest = |sort: &str| Term::variable(Variable::new("Rest", Sort::simple(sort)));
    let mut edits = Vec::new();
    match term.kind() {
        TermKind::Map {
            definition,
            entries,
            rest: own,
        } => {
            edits.push((
                Edit::Rest,
                Term::map(
                    definition.clone(),
                    entries.to_vec(),
                    own.is_none().then(|| rest(definition.map_sort.as_ref())),
                ),
            ));
            let mut other = (**definition).clone();
            other.key_sort = other_element_sort(&definition.key_sort);
            edits.push((
                Edit::Definition,
                Term::map(Arc::new(other), entries.to_vec(), own.clone()),
            ));
        }
        TermKind::Set {
            definition,
            elements,
            rest: own,
        } => {
            edits.push((
                Edit::Rest,
                Term::set(
                    definition.clone(),
                    elements.to_vec(),
                    own.is_none().then(|| rest(definition.list_sort.as_ref())),
                ),
            ));
            let mut other = (**definition).clone();
            other.element_sort = other_element_sort(&definition.element_sort);
            edits.push((
                Edit::Definition,
                Term::set(Arc::new(other), elements.to_vec(), own.clone()),
            ));
        }
        TermKind::List {
            definition,
            heads,
            rest: own,
        } => {
            edits.push((
                Edit::Rest,
                Term::list(
                    definition.clone(),
                    heads.to_vec(),
                    own.is_none()
                        .then(|| (rest(definition.list_sort.as_ref()), Vec::new())),
                ),
            ));
            let mut other = (**definition).clone();
            other.element_sort = other_element_sort(&definition.element_sort);
            edits.push((
                Edit::Definition,
                Term::list(
                    Arc::new(other),
                    heads.to_vec(),
                    own.clone().map(|(middle, tails)| (middle, tails.to_vec())),
                ),
            ));
        }
        TermKind::DomainValue { sort, value } => {
            edits.push((
                Edit::Sort,
                Term::domain_value(other_sort(sort), value.as_bytes().to_vec()),
            ));
            let mut changed = value.as_bytes().to_vec();
            changed.push(b'1');
            edits.push((Edit::Value, Term::domain_value(sort.clone(), changed)));
        }
        TermKind::Variable(variable) => {
            let mut changed = variable.clone();
            changed.sort = other_sort(&variable.sort);
            edits.push((Edit::Sort, Term::variable(changed)));
            let mut renamed = variable.clone();
            renamed.name = format!("{}'", variable.name).into();
            edits.push((Edit::Name, Term::variable(renamed)));
        }
        TermKind::Injection {
            source,
            target,
            term,
        } => {
            edits.push((
                Edit::Sort,
                Term::injection(other_sort(source), target.clone(), term.clone()),
            ));
            edits.push((
                Edit::Sort,
                Term::injection(source.clone(), other_sort(target), term.clone()),
            ));
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => {
            let mut sorts = sort_arguments.clone();
            match sorts.first_mut() {
                Some(first) => *first = other_sort(first),
                None => sorts.push(Sort::builtin(BuiltinSort::Int)),
            }
            edits.push((
                Edit::Sort,
                Term::application(symbol.clone(), sorts, arguments.clone()),
            ));
            let mut renamed = (**symbol).clone();
            renamed.name = format!("{}'", symbol.name).into();
            edits.push((
                Edit::Symbol,
                Term::application(Arc::new(renamed), sort_arguments.clone(), arguments.clone()),
            ));
        }
        TermKind::And(..) => {}
    }
    edits
}

/// Every term that differs from `term` in one field of one node (a one-edit neighbour), with
/// the field: a collection's rest added or removed or its definition swapped, one sort (an
/// injection's source and its target separately), a variable's name, one symbol, one domain
/// value. A
/// comparison is decided by the first field in which two terms differ, so a pair that differs
/// in one field is the pair that reaches the arm comparing that field with every field before
/// it equal; independent draws rarely give one at depth. The neighbours are built by the public
/// constructors, so a map or set neighbour is sorted again.
pub(in crate::tests) fn one_edit_neighbours(term: &Term) -> Vec<(Edit, Term)> {
    let mut neighbours = root_edits(term);
    let rebuilt = |index: usize, child: Term| -> Term {
        match term.kind() {
            TermKind::And(left, right) => {
                if index == 0 {
                    Term::and(child, right.clone())
                } else {
                    Term::and(left.clone(), child)
                }
            }
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } => {
                let mut arguments = arguments.clone();
                arguments[index] = child;
                Term::application(symbol.clone(), sort_arguments.clone(), arguments)
            }
            TermKind::Injection { source, target, .. } => {
                Term::injection(source.clone(), target.clone(), child)
            }
            TermKind::Map {
                definition,
                entries,
                rest,
            } => {
                let mut entries = entries.to_vec();
                let mut rest = rest.clone();
                if index < 2 * entries.len() {
                    let entry = &mut entries[index / 2];
                    if index.is_multiple_of(2) {
                        entry.0 = child;
                    } else {
                        entry.1 = child;
                    }
                } else {
                    rest = Some(child);
                }
                Term::map(definition.clone(), entries, rest)
            }
            TermKind::Set {
                definition,
                elements,
                rest,
            } => {
                let mut elements = elements.to_vec();
                let mut rest = rest.clone();
                if index < elements.len() {
                    elements[index] = child;
                } else {
                    rest = Some(child);
                }
                Term::set(definition.clone(), elements, rest)
            }
            TermKind::List {
                definition,
                heads,
                rest,
            } => {
                let mut heads = heads.to_vec();
                let mut rest = rest.clone().map(|(middle, tails)| (middle, tails.to_vec()));
                if index < heads.len() {
                    heads[index] = child;
                } else if let Some((middle, tail)) = &mut rest {
                    if index == heads.len() {
                        *middle = child;
                    } else {
                        tail[index - heads.len() - 1] = child;
                    }
                }
                Term::list(definition.clone(), heads, rest)
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {
                unreachable!("a leaf has no child")
            }
        }
    };
    let children: Vec<Term> = match term.kind() {
        TermKind::And(left, right) => vec![left.clone(), right.clone()],
        TermKind::Application { arguments, .. } => arguments.clone(),
        TermKind::Injection { term, .. } => vec![term.clone()],
        TermKind::Map { entries, rest, .. } => entries
            .iter()
            .flat_map(|(key, value)| [key.clone(), value.clone()])
            .chain(rest.clone())
            .collect(),
        TermKind::Set { elements, rest, .. } => {
            elements.iter().cloned().chain(rest.clone()).collect()
        }
        TermKind::List { heads, rest, .. } => {
            let mut children = heads.to_vec();
            if let Some((middle, tail)) = rest {
                children.push(middle.clone());
                children.extend(tail.iter().cloned());
            }
            children
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => Vec::new(),
    };
    for (index, child) in children.iter().enumerate() {
        for (edit, neighbour) in one_edit_neighbours(child) {
            neighbours.push((edit, rebuilt(index, neighbour)));
        }
    }
    neighbours
}

/// The classes the documentation of [`term`] and [`term_with_ground_keys`] names, counted over
/// their terms: two definitions per collection kind, domain values that are not UTF-8, k cells
/// at the root and below it, and maps and sets whose keys share one header, have different
/// headers, or repeat a key under different values.
#[derive(Debug, Default)]
struct GeneratedClasses {
    /// `(kind, the second definition)` of each collection.
    definitions: std::collections::BTreeSet<(&'static str, bool)>,
    not_utf8: usize,
    k_cell_at_root: usize,
    k_cell_below: usize,
    shared_header: usize,
    different_headers: usize,
    equal_keys_different_values: usize,
}

/// The header of a key: what a key's root reads before its children.
fn header(key: &Term) -> String {
    match key.kind() {
        TermKind::DomainValue { sort, .. } => format!("value {sort:?}"),
        TermKind::Injection { source, target, .. } => format!("injection {source:?} {target:?}"),
        TermKind::Application { symbol, .. } => format!("application {}", symbol.name),
        TermKind::Variable(_) => "variable".into(),
        TermKind::And(..) => "and".into(),
        TermKind::Map { .. } => "map".into(),
        TermKind::List { .. } => "list".into(),
        TermKind::Set { .. } => "set".into(),
    }
}

impl GeneratedClasses {
    fn count(&mut self, term: &Term, depth: usize) {
        let mut keys = |keys: Vec<&Term>| {
            if keys.len() > 1 {
                let first = header(keys[0]);
                if keys.iter().all(|key| header(key) == first) {
                    self.shared_header += 1;
                } else {
                    self.different_headers += 1;
                }
            }
        };
        match term.kind() {
            TermKind::DomainValue { value, .. } => {
                self.not_utf8 += usize::from(std::str::from_utf8(value.as_bytes()).is_err());
            }
            TermKind::Application { symbol, .. } => {
                if symbol.name.as_ref() == WellKnownSymbol::KCell.as_str() {
                    if depth == 0 {
                        self.k_cell_at_root += 1;
                    } else {
                        self.k_cell_below += 1;
                    }
                }
            }
            TermKind::Map {
                definition,
                entries,
                ..
            } => {
                self.definitions
                    .insert(("map", definition.key_sort == element_sort(true)));
                keys(entries.iter().map(|(key, _)| key).collect());
                self.equal_keys_different_values +=
                    usize::from(entries.iter().enumerate().any(|(index, (key, value))| {
                        entries
                            .range(index + 1..)
                            .any(|(other, other_value)| other == key && other_value != value)
                    }));
            }
            TermKind::Set {
                definition,
                elements,
                ..
            } => {
                self.definitions
                    .insert(("set", definition.element_sort == element_sort(true)));
                keys(elements.iter().collect());
            }
            TermKind::List { definition, .. } => {
                self.definitions
                    .insert(("list", definition.element_sort == element_sort(true)));
            }
            TermKind::And(..) | TermKind::Variable(_) | TermKind::Injection { .. } => {}
        }
        let children: Vec<&Term> = match term.kind() {
            TermKind::And(left, right) => vec![left, right],
            TermKind::Application { arguments, .. } => arguments.iter().collect(),
            TermKind::Injection { term, .. } => vec![term],
            TermKind::Map { entries, rest, .. } => entries
                .iter()
                .flat_map(|(key, value)| [key, value])
                .chain(rest)
                .collect(),
            TermKind::Set { elements, rest, .. } => elements.iter().chain(rest).collect(),
            TermKind::List { heads, rest, .. } => {
                let mut children = heads.iter().collect::<Vec<_>>();
                if let Some((middle, tail)) = rest {
                    children.push(middle);
                    children.extend(tail);
                }
                children
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => Vec::new(),
        };
        for child in children {
            self.count(child, depth + 1);
        }
    }
}

/// Every class the generators' documentation names occurs in their terms.
#[test]
fn the_generators_produce_the_classes_their_documentation_names() {
    use proptest::{
        strategy::ValueTree,
        test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
    };
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let mut classes = GeneratedClasses::default();
    for strategy in [term().boxed(), term_with_ground_keys().boxed()] {
        for _ in 0..1024 {
            classes.count(
                &strategy.new_tree(&mut runner).expect("a case").current(),
                0,
            );
        }
    }
    eprintln!("generated classes: {classes:?}");
    for kind in ["map", "set", "list"] {
        for second in [false, true] {
            assert!(
                classes.definitions.contains(&(kind, second)),
                "no {kind} of definition {}",
                u8::from(second) + 1
            );
        }
    }
    for (count, class) in [
        (classes.not_utf8, "domain value that is not UTF-8"),
        (classes.k_cell_at_root, "k cell at the root"),
        (classes.k_cell_below, "k cell below the root"),
        (
            classes.shared_header,
            "collection whose keys share one header",
        ),
        (
            classes.different_headers,
            "collection with keys of different headers",
        ),
        (
            classes.equal_keys_different_values,
            "map with a key repeated under different values",
        ),
    ] {
        assert!(count > 0, "no {class}");
    }
}
