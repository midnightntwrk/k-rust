//! Property tests of the hypotheses that lean/KRust/TermAttributes.lean takes about the term
//! representation (the hypothesis table in lean/README.md):
//! - `TotalOrder.trans` and `TotalOrder.antisym`: `Ord for Term` is transitive, and
//!   `a.cmp(b) == Equal` exactly when `a == b`, which is structural equality of the kinds;
//! - `WF`: map entries are sorted by `(key, value)` and set elements are sorted with adjacent
//!   elements distinct, at every depth of a term built by the public constructors.
//!
//! Terms are built directly through the public constructors of `k_rust_backend::term`, over small
//! alphabets so that equal and nearly equal terms are frequent: symbols that share a name but
//! differ in one attribute, sorts that differ in one argument, variables that differ only in
//! kind or sort, collections that differ only in their definition, integer values with two
//! spellings. Every `build` allocates fresh `Arc`s, so equal terms are compared through their
//! hash and kind, never through pointer identity alone.

use std::{cmp::Ordering, sync::Arc};

use k_rust_backend::term::{
    CollectionSymbols, FunctionType, ListDefinition, MapDefinition, Sort, Symbol, SymbolType, Term,
    TermKind, Variable, VariableKind,
};
use k_rust_kore::names::BuiltinSort;
use proptest::prelude::*;

/// A term to build: every index selects from a small pool, so that collisions are frequent.
#[derive(Clone, Debug)]
enum Spec {
    Dv {
        sort: u8,
        value: u8,
    },
    Var {
        set: bool,
        sort: u8,
        name: u8,
    },
    App {
        symbol: u8,
        sorts: Vec<u8>,
        args: Vec<Spec>,
    },
    Inj {
        source: u8,
        target: u8,
        term: Box<Spec>,
    },
    And(Box<Spec>, Box<Spec>),
    Map {
        definition: u8,
        entries: Vec<(Spec, Spec)>,
        rest: Option<Box<Spec>>,
    },
    List {
        definition: u8,
        heads: Vec<Spec>,
        rest: Option<(Box<Spec>, Vec<Spec>)>,
    },
    Set {
        definition: u8,
        elements: Vec<Spec>,
        rest: Option<Box<Spec>>,
    },
}

const SORTS: u8 = 5;
const VALUES: u8 = 4;
const SYMBOLS: u8 = 5;
const DEFINITIONS: u8 = 2;

fn sort(index: u8) -> Sort {
    match index % SORTS {
        0 => Sort::simple("SortA"),
        1 => Sort::simple("SortB"),
        2 => Sort::application("SortList", vec![Sort::simple("SortA")]),
        3 => Sort::Variable(Arc::from("S")),
        _ => Sort::builtin(BuiltinSort::Int),
    }
}

/// `"01"` is canonicalized to `"1"` in the `Int` sort and kept verbatim elsewhere.
fn value(index: u8) -> &'static str {
    ["0", "1", "2", "01"][usize::from(index % VALUES)]
}

/// Symbols named `c` differ from each other in exactly one attribute.
fn symbol(index: u8) -> Arc<Symbol> {
    let mut symbol = Symbol::constructor(
        if index % SYMBOLS == 1 { "d" } else { "c" },
        Vec::new(),
        Sort::simple("SortA"),
    );
    match index % SYMBOLS {
        2 => symbol.attributes.macro_or_alias = true,
        3 => symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Partial),
        4 => symbol.attributes.injective = true,
        _ => {}
    }
    Arc::new(symbol)
}

fn collection_symbols(prefix: &str) -> CollectionSymbols {
    CollectionSymbols {
        unit: Arc::from(format!("{prefix}unit")),
        element: Arc::from(format!("{prefix}element")),
        concat: Arc::from(format!("{prefix}concat")),
    }
}

/// Two map definitions that differ only in the key sort.
fn map_definition(index: u8) -> Arc<MapDefinition> {
    Arc::new(MapDefinition {
        symbols: collection_symbols("Map"),
        key_sort: Arc::from(if index.is_multiple_of(DEFINITIONS) {
            "SortA"
        } else {
            "SortB"
        }),
        value_sort: Arc::from("SortA"),
        map_sort: Arc::from("SortMap"),
    })
}

/// Two list (and set) definitions that differ only in the element sort.
fn list_definition(prefix: &str, index: u8) -> Arc<ListDefinition> {
    Arc::new(ListDefinition {
        symbols: collection_symbols(prefix),
        element_sort: Arc::from(if index.is_multiple_of(DEFINITIONS) {
            "SortA"
        } else {
            "SortB"
        }),
        list_sort: Arc::from(format!("Sort{prefix}")),
    })
}

impl Spec {
    /// Build the term through the public constructors, with fresh allocations.
    fn build(&self) -> Term {
        match self {
            Self::Dv { sort: s, value: v } => Term::domain_value(sort(*s), value(*v)),
            Self::Var { set, sort: s, name } => {
                let name = format!("X{name}");
                Term::variable(if *set {
                    Variable::set(name, sort(*s))
                } else {
                    Variable::new(name, sort(*s))
                })
            }
            Self::App {
                symbol: f,
                sorts,
                args,
            } => Term::application(
                symbol(*f),
                sorts.iter().map(|s| sort(*s)).collect(),
                args.iter().map(Self::build).collect(),
            ),
            Self::Inj {
                source,
                target,
                term,
            } => Term::injection(sort(*source), sort(*target), term.build()),
            Self::And(left, right) => Term::and(left.build(), right.build()),
            Self::Map {
                definition,
                entries,
                rest,
            } => Term::map(
                map_definition(*definition),
                entries
                    .iter()
                    .map(|(key, value)| (key.build(), value.build()))
                    .collect(),
                rest.as_ref().map(|rest| rest.build()),
            ),
            Self::List {
                definition,
                heads,
                rest,
            } => Term::list(
                list_definition("List", *definition),
                heads.iter().map(Self::build).collect(),
                rest.as_ref().map(|(middle, tails)| {
                    (middle.build(), tails.iter().map(Self::build).collect())
                }),
            ),
            Self::Set {
                definition,
                elements,
                rest,
            } => Term::set(
                list_definition("Set", *definition),
                elements.iter().map(Self::build).collect(),
                rest.as_ref().map(|rest| rest.build()),
            ),
        }
    }

    /// The number of nodes, the range of `mutate`'s position.
    fn size(&self) -> usize {
        let sum = |specs: &[Self]| specs.iter().map(Self::size).sum::<usize>();
        1 + match self {
            Self::Dv { .. } | Self::Var { .. } => 0,
            Self::App { args, .. } => sum(args),
            Self::Inj { term, .. } => term.size(),
            Self::And(left, right) => left.size() + right.size(),
            Self::Map { entries, rest, .. } => {
                entries
                    .iter()
                    .map(|(key, value)| key.size() + value.size())
                    .sum::<usize>()
                    + rest.as_ref().map_or(0, |rest| rest.size())
            }
            Self::List { heads, rest, .. } => {
                sum(heads)
                    + rest
                        .as_ref()
                        .map_or(0, |(middle, tails)| middle.size() + sum(tails))
            }
            Self::Set { elements, rest, .. } => {
                sum(elements) + rest.as_ref().map_or(0, |rest| rest.size())
            }
        }
    }

    /// Change one local choice of the `*position`-th node in preorder (counting down), and
    /// leave the rest of the term as it is: a near miss of the original term.
    fn mutate(&self, position: &mut usize) -> Self {
        let here = *position == 0;
        *position = position.wrapping_sub(1);
        let children = |specs: &[Self], position: &mut usize| -> Vec<Self> {
            specs.iter().map(|spec| spec.mutate(position)).collect()
        };
        match self {
            Self::Dv { sort, value } if here => Self::Dv {
                sort: *sort,
                value: value.wrapping_add(1),
            },
            Self::Var { set, sort, name } if here => Self::Var {
                set: !set,
                sort: *sort,
                name: *name,
            },
            Self::Dv { .. } | Self::Var { .. } => self.clone(),
            Self::App {
                symbol,
                sorts,
                args,
            } => Self::App {
                symbol: if here {
                    symbol.wrapping_add(1)
                } else {
                    *symbol
                },
                sorts: sorts.clone(),
                args: children(args, position),
            },
            Self::Inj {
                source,
                target,
                term,
            } => Self::Inj {
                source: if here {
                    source.wrapping_add(1)
                } else {
                    *source
                },
                target: *target,
                term: Box::new(term.mutate(position)),
            },
            Self::And(left, right) if here => Self::And(right.clone(), left.clone()),
            Self::And(left, right) => Self::And(
                Box::new(left.mutate(position)),
                Box::new(right.mutate(position)),
            ),
            Self::Map {
                definition,
                entries,
                rest,
            } => Self::Map {
                definition: if here {
                    definition.wrapping_add(1)
                } else {
                    *definition
                },
                entries: entries
                    .iter()
                    .map(|(key, value)| (key.mutate(position), value.mutate(position)))
                    .collect(),
                rest: rest.as_ref().map(|rest| Box::new(rest.mutate(position))),
            },
            Self::List {
                definition,
                heads,
                rest,
            } => Self::List {
                definition: if here {
                    definition.wrapping_add(1)
                } else {
                    *definition
                },
                heads: children(heads, position),
                rest: rest.as_ref().map(|(middle, tails)| {
                    (Box::new(middle.mutate(position)), children(tails, position))
                }),
            },
            Self::Set {
                definition,
                elements,
                rest,
            } => Self::Set {
                definition: if here {
                    definition.wrapping_add(1)
                } else {
                    *definition
                },
                elements: children(elements, position),
                rest: rest.as_ref().map(|rest| Box::new(rest.mutate(position))),
            },
        }
    }
}

fn spec() -> impl Strategy<Value = Spec> {
    let leaf = prop_oneof![
        (0..SORTS, 0..VALUES).prop_map(|(sort, value)| Spec::Dv { sort, value }),
        (any::<bool>(), 0..SORTS, 0u8..2).prop_map(|(set, sort, name)| Spec::Var {
            set,
            sort,
            name
        }),
    ];
    leaf.prop_recursive(3, 24, 3, |inner| {
        let items = prop::collection::vec(inner.clone(), 0..3);
        prop_oneof![
            (
                0..SYMBOLS,
                prop::collection::vec(0..SORTS, 0..2),
                items.clone()
            )
                .prop_map(|(symbol, sorts, args)| Spec::App {
                    symbol,
                    sorts,
                    args
                }),
            (0..SORTS, 0..SORTS, inner.clone()).prop_map(|(source, target, term)| Spec::Inj {
                source,
                target,
                term: Box::new(term),
            }),
            (inner.clone(), inner.clone())
                .prop_map(|(left, right)| Spec::And(Box::new(left), Box::new(right))),
            (
                0..DEFINITIONS,
                prop::collection::vec((inner.clone(), inner.clone()), 0..4),
                prop::option::of(inner.clone())
            )
                .prop_map(|(definition, entries, rest)| Spec::Map {
                    definition,
                    entries,
                    rest: rest.map(Box::new),
                }),
            (
                0..DEFINITIONS,
                items.clone(),
                prop::option::of((inner.clone(), items.clone()))
            )
                .prop_map(|(definition, heads, rest)| Spec::List {
                    definition,
                    heads,
                    rest: rest.map(|(middle, tails)| (Box::new(middle), tails)),
                }),
            (
                0..DEFINITIONS,
                prop::collection::vec(inner.clone(), 0..4),
                prop::option::of(inner)
            )
                .prop_map(|(definition, elements, rest)| Spec::Set {
                    definition,
                    elements,
                    rest: rest.map(Box::new),
                }),
        ]
    })
}

/// A term and a relative of it: the same term built again, a near miss, the same node changed
/// twice (so that `base`, one change and two changes at one position form a chain of three
/// neighbours), or an independent term.
fn related(base: &Spec, choice: u8, position: usize, other: &Spec) -> Spec {
    let position = position % base.size();
    match choice % 4 {
        0 => base.clone(),
        1 => base.mutate(&mut position.clone()),
        2 => base
            .mutate(&mut position.clone())
            .mutate(&mut position.clone()),
        _ => other.clone(),
    }
}

/// `le` of the Lean model: `a <= b` under `Ord for Term`.
fn le(a: &Term, b: &Term) -> bool {
    a.cmp(b) != Ordering::Greater
}

/// The model's `WF`, checked at every depth: map entries sorted by `(key, value)`, set elements
/// sorted with adjacent elements distinct.
fn check_wf(term: &Term) -> Result<(), String> {
    match term.kind() {
        TermKind::And(left, right) => {
            check_wf(left)?;
            check_wf(right)
        }
        TermKind::Application { arguments, .. } => arguments.iter().try_for_each(check_wf),
        TermKind::DomainValue { .. } | TermKind::Variable(_) => Ok(()),
        TermKind::Injection { term, .. } => check_wf(term),
        TermKind::Map { entries, rest, .. } => {
            if let Some(pair) = entries.windows(2).find(|pair| pair[0] > pair[1]) {
                return Err(format!("map entries out of order: {pair:?}"));
            }
            for (key, value) in entries {
                check_wf(key)?;
                check_wf(value)?;
            }
            rest.iter().try_for_each(check_wf)
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().try_for_each(check_wf)?;
            if let Some((middle, tails)) = rest {
                check_wf(middle)?;
                tails.iter().try_for_each(check_wf)?;
            }
            Ok(())
        }
        TermKind::Set { elements, rest, .. } => {
            if let Some(pair) = elements
                .windows(2)
                .find(|pair| !(le(&pair[0], &pair[1]) && pair[0] != pair[1]))
            {
                return Err(format!("set elements not strictly sorted: {pair:?}"));
            }
            elements.iter().try_for_each(check_wf)?;
            rest.iter().try_for_each(check_wf)
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    /// `TotalOrder.antisym` (and its converse): `a.cmp(b) == Equal` exactly when `a == b`, and
    /// `a == b` exactly when the kinds are equal, which is the model's equality.
    #[test]
    fn ord_for_term_equal_is_eq(
        base in spec(),
        other in spec(),
        choice in any::<u8>(),
        position in 0usize..32,
    ) {
        let a = base.build();
        let b = related(&base, choice, position, &other).build();
        prop_assert_eq!(a.cmp(&b) == Ordering::Equal, a == b, "{:?} vs {:?}", a, b);
        prop_assert_eq!(a == b, a.kind() == b.kind(), "{:?} vs {:?}", a, b);
        prop_assert_eq!(b.cmp(&a), a.cmp(&b).reverse());
    }

    /// `TotalOrder.trans`: `a <= b` and `b <= c` give `a <= c`, for every order of a triple of
    /// related terms.
    #[test]
    fn ord_for_term_is_transitive(
        base in spec(),
        other in spec(),
        choices in any::<(u8, u8)>(),
        positions in (0usize..32, 0usize..32),
        same_position in any::<bool>(),
    ) {
        let second = if same_position { positions.0 } else { positions.1 };
        let terms = [
            base.build(),
            related(&base, choices.0, positions.0, &other).build(),
            related(&base, choices.1, second, &other).build(),
        ];
        for (i, j, k) in [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)] {
            let (a, b, c) = (&terms[i], &terms[j], &terms[k]);
            if le(a, b) && le(b, c) {
                prop_assert!(le(a, c), "{:?} <= {:?} <= {:?} but not {:?} <= {:?}", a, b, c, a, c);
            }
        }
    }

    /// `WF`: every term the public constructors build has sorted map entries and strictly sorted
    /// set elements at every depth. `Term::new` is private and `Term::map` and `Term::set` are the
    /// only constructors of a map or set kind (`with_evaluated_cache` copies an existing kind), so
    /// generating over those constructors with arbitrary children covers every built term.
    #[test]
    fn constructed_collections_are_sorted(base in spec()) {
        let term = base.build();
        prop_assert!(check_wf(&term).is_ok(), "{}", check_wf(&term).unwrap_err());
    }

    #[test]
    fn map_order_fast_path_agrees_with_sort_and_dedup(
        entries in prop::collection::vec((spec(), spec()), 0..16),
        nested in prop::collection::vec((spec(), spec()), 0..8),
    ) {
        let definition = map_definition(0);
        let entries: Vec<_> = entries.into_iter().map(|(key, value)| (key.build(), value.build())).collect();
        let nested: Vec<_> = nested.into_iter().map(|(key, value)| (key.build(), value.build())).collect();
        let general = Term::map(definition.clone(), entries.clone(), None);
        let mut sorted = entries.clone();
        sorted.sort();
        sorted.dedup();
        let fast = Term::map(definition.clone(), sorted, None);
        prop_assert_eq!(fast, general);
        let rest = Term::map(definition.clone(), nested, None);
        let actual = Term::map(definition.clone(), entries.clone(), Some(rest.clone()));
        let mut expected_entries = entries;
        let TermKind::Map { entries: rest_entries, .. } = rest.kind() else {
            unreachable!()
        };
        expected_entries.extend(rest_entries.iter().cloned());
        expected_entries.sort();
        expected_entries.dedup();
        let expected = Term::map(definition, expected_entries, None);
        prop_assert_eq!(actual, expected);
    }
}

/// Fixed near misses the generator reaches only by chance: collection definitions that differ in
/// one field, sets that receive duplicates, and the integer spellings `1` and `01`.
#[test]
fn fixed_near_misses_agree_with_equality() {
    let one = Term::domain_value(Sort::builtin(BuiltinSort::Int), "1");
    let one_again = Term::domain_value(Sort::builtin(BuiltinSort::Int), "01");
    assert_eq!(one, one_again);
    assert_eq!(one.cmp(&one_again), Ordering::Equal);

    let set = |definition| {
        Term::set(
            list_definition("Set", definition),
            vec![one.clone(), one_again.clone(), one.clone()],
            None,
        )
    };
    let TermKind::Set { elements, .. } = set(0).kind().clone() else {
        panic!("a set with elements is a set");
    };
    assert_eq!(elements.len(), 1);
    assert_ne!(set(0), set(1));
    assert_ne!(set(0).cmp(&set(1)), Ordering::Equal);
    assert_eq!(set(0), set(0));
    assert_eq!(set(0).cmp(&set(0)), Ordering::Equal);

    let x = |kind| {
        Term::variable(Variable {
            kind,
            sort: sort(0),
            name: Arc::from("X"),
        })
    };
    assert_ne!(x(VariableKind::Element), x(VariableKind::Set));
    assert_ne!(
        x(VariableKind::Element).cmp(&x(VariableKind::Set)),
        Ordering::Equal
    );
}
