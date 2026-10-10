//! Which declarations of a `LIST`, `SET` or `MAP` hook denote a value of their result sort; a
//! responsibility, not an algorithm; no counter of its own, no worklist.
//!
//! A hooked symbol `f : S1 ... Sn -> S` denotes a value of `S` whatever computes it, and KORE has
//! no implicit subsorting. A hook that builds a collection builds it from what its arguments
//! give it: an element argument, the elements (keys, values, entries) of a collection argument.
//! Each of those is an element of the result exactly when its sort is the result's element
//! (key, value) sort or a subsort of it, whose values are elements once injected
//! ([`super::ResultCollection`]). A hook that returns one element of a collection argument (a
//! list's element, a map's value, or a default argument) gives a value of `S` exactly when that
//! element's sort is `S` or a subsort of it.
//!
//! Any other declaration says that the hook gives a value of `S` that it does not give in
//! general: `makeBad(Int, Int) : Vals [hook(LIST.make)]` on a list of `Val` would build a list
//! of `Val` holding an `Int`, and `Int ::= Vals "[" Int "]" [hook(LIST.get)]` an `Int` that is a
//! `Val`. Such a declaration has no model in which the hook computes the symbol, so the
//! definition is rejected where the symbol is declared ([`misfit`]). The rule is stated over the
//! facts [`SortFacts`] names, so the frontend decides a declaration with it before it emits one,
//! in the definition's own sorts, and the loader decides KORE from any producer the same way.
//!
//! An argument that is only read (an index, a key looked up or removed, a set whose elements are
//! removed) is not moved into the result, so its sort decides nothing here.

use crate::{
    matching::SortGraph,
    term::{CollectionMetadata, Name, Sort},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind {
    List,
    Set,
    Map,
}

impl Kind {
    const fn noun(self) -> &'static str {
        match self {
            Self::List => "list",
            Self::Set => "set",
            Self::Map => "map",
        }
    }
}

/// What a hook does with one argument.
#[derive(Clone, Copy, Debug)]
enum Operand {
    /// Read, not moved into the result.
    Read,
    /// An element of the list or set result.
    Element,
    /// A key of the map result.
    Key,
    /// A value of the map result.
    Value,
    /// A collection of this kind whose elements (entries) are elements (entries) of the result.
    Elements(Kind),
    /// A map whose keys are elements of the result.
    Keys,
    /// A map whose values are elements of the result.
    Values,
    /// A collection of this kind one of whose elements (a list's) or values (a map's) is the
    /// result.
    Source(Kind),
    /// A value the hook may give as its result.
    Alternative,
}

/// What a hook gives.
#[derive(Clone, Copy, Debug)]
enum Gives {
    Collection(Kind),
    /// An element of its `Source` argument, or its `Alternative` argument.
    Member,
}

/// The arguments and the result of `hook`, for the collection hooks that build a collection or
/// return one of a collection's elements; `None` for every other hook.
fn signature(hook: &str) -> Option<(&'static [Operand], Gives)> {
    use Operand::{Alternative, Element, Elements, Key, Keys, Read, Source, Value, Values};
    let list = Gives::Collection(Kind::List);
    let set = Gives::Collection(Kind::Set);
    let map = Gives::Collection(Kind::Map);
    Some(match hook {
        "LIST.unit" => (&[], list),
        "LIST.element" => (&[Element], list),
        "LIST.concat" => (&[Elements(Kind::List), Elements(Kind::List)], list),
        "LIST.make" => (&[Read, Element], list),
        "LIST.range" => (&[Elements(Kind::List), Read, Read], list),
        "LIST.update" => (&[Elements(Kind::List), Read, Element], list),
        "LIST.updateAll" => (&[Elements(Kind::List), Read, Elements(Kind::List)], list),
        "LIST.get" => (&[Source(Kind::List), Read], Gives::Member),
        "SET.unit" => (&[], set),
        "SET.element" => (&[Element], set),
        "SET.concat" => (&[Elements(Kind::Set), Elements(Kind::Set)], set),
        "SET.difference" | "SET.intersection" => (&[Elements(Kind::Set), Read], set),
        "SET.list2set" => (&[Elements(Kind::List)], set),
        "SET.set2list" => (&[Elements(Kind::Set)], list),
        "MAP.unit" => (&[], map),
        "MAP.element" => (&[Key, Value], map),
        "MAP.concat" | "MAP.updateAll" => (&[Elements(Kind::Map), Elements(Kind::Map)], map),
        "MAP.update" => (&[Elements(Kind::Map), Key, Value], map),
        "MAP.remove" | "MAP.removeAll" => (&[Elements(Kind::Map), Read], map),
        "MAP.keys" => (&[Keys], set),
        "MAP.keys_list" => (&[Keys], list),
        "MAP.values" => (&[Values], list),
        "MAP.lookup" => (&[Source(Kind::Map), Read], Gives::Member),
        "MAP.lookupOrDefault" => (&[Source(Kind::Map), Read, Alternative], Gives::Member),
        _ => return None,
    })
}

/// Whether `hook` gives one element of a collection argument (or a default) as its result, which
/// is then a value of the application's sort once injected ([`member_of_result`]).
pub(crate) fn gives_member(hook: &str) -> bool {
    matches!(signature(hook), Some((_, Gives::Member)))
}

/// `value`, an element `hook` gives, as a value of `result_sort`: itself when its sort is
/// `result_sort`, its injection when that is a strict subsort, `None` otherwise (a declaration
/// [`misfit`] rejects). Without a declared result sort the value is the hook's own.
pub(crate) fn member_of_result(
    value: crate::term::Term,
    result_sort: Option<&Sort>,
    sorts: Option<&SortGraph>,
) -> Option<crate::term::Term> {
    let Some(result_sort) = result_sort else {
        return Some(value);
    };
    let from = value.sort();
    if from == *result_sort {
        return Some(value);
    }
    let below =
        sorts.is_some_and(|sorts| matches!(sorts.check_subsort(&from, result_sort), Ok(true)));
    below.then(|| crate::term::Term::injection(from, result_sort.clone(), value))
}

/// What a collection holds, in the sorts of the definition at hand: a list's or set's element
/// sort, a map's key and value sorts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CollectionShape<S> {
    List(S),
    Set(S),
    Map { key: S, value: S },
}

impl<S> CollectionShape<S> {
    const fn kind(&self) -> Kind {
        match self {
            Self::List(_) => Kind::List,
            Self::Set(_) => Kind::Set,
            Self::Map { .. } => Kind::Map,
        }
    }
}

/// The facts about a definition's sorts on which [`misfit`] decides: which sorts are collections
/// and of what, and the subsort order. A definition supplies them in its own sorts, so the same
/// rule decides a definition before it is emitted and the KORE that is loaded.
pub trait SortFacts {
    type Sort;
    /// The collection `sort` is, if it is a collection sort.
    fn collection(&self, sort: &Self::Sort) -> Option<CollectionShape<Self::Sort>>;
    /// Whether `sub` is `sup` or a subsort of it.
    fn below(&self, sub: &Self::Sort, sup: &Self::Sort) -> bool;
    /// `sort` as the reason names it.
    fn render(&self, sort: &Self::Sort) -> String;
}

/// The facts of a loaded definition: the collection of each collection sort and the closure of
/// its subsort axioms.
pub(crate) struct LoadedSorts<'a, C> {
    pub(crate) collection: C,
    pub(crate) sorts: &'a SortGraph,
}

impl<'c, C: Fn(&Sort) -> Option<&'c CollectionMetadata>> SortFacts for LoadedSorts<'_, C> {
    type Sort = Sort;

    fn collection(&self, sort: &Sort) -> Option<CollectionShape<Sort>> {
        let named = |name: &Name| Sort::simple(name.clone());
        (self.collection)(sort).map(|collection| match collection {
            CollectionMetadata::List(definition) => {
                CollectionShape::List(named(&definition.element_sort))
            }
            CollectionMetadata::Set(definition) => {
                CollectionShape::Set(named(&definition.element_sort))
            }
            CollectionMetadata::Map(definition) => CollectionShape::Map {
                key: named(&definition.key_sort),
                value: named(&definition.value_sort),
            },
        })
    }

    fn below(&self, sub: &Sort, sup: &Sort) -> bool {
        matches!(self.sorts.check_subsort(sub, sup), Ok(true))
    }

    fn render(&self, sort: &Sort) -> String {
        render(sort)
    }
}

/// Why a symbol `argument_sorts -> result_sort` hooked to `hook` denotes no value of
/// `result_sort` in general, or `None` when it does or `hook` is no hook of [`signature`].
pub fn misfit<F: SortFacts>(
    hook: &str,
    argument_sorts: &[F::Sort],
    result_sort: &F::Sort,
    facts: &F,
) -> Option<String> {
    let (operands, gives) = signature(hook)?;
    if operands.len() != argument_sorts.len() {
        return Some(format!(
            "{hook} takes {} arguments, the symbol {}",
            operands.len(),
            argument_sorts.len()
        ));
    }
    let of_kind = |sort: &F::Sort, kind: Kind| {
        facts
            .collection(sort)
            .filter(|collection| collection.kind() == kind)
    };
    let result = match gives {
        Gives::Collection(kind) => match of_kind(result_sort, kind) {
            Some(result) => Some(result),
            None => {
                return Some(format!(
                    "{hook} gives a {}, but the result sort {} is no {} sort",
                    kind.noun(),
                    facts.render(result_sort),
                    kind.noun()
                ));
            }
        },
        Gives::Member => None,
    };
    // The sorts of what the result holds: a list's or set's elements, a map's keys and values.
    let (element, key, value) = match result {
        Some(CollectionShape::List(element) | CollectionShape::Set(element)) => {
            (Some(element), None, None)
        }
        Some(CollectionShape::Map { key, value }) => (None, Some(key), Some(value)),
        None => (None, None, None),
    };
    // `moved`, of sort `from` (described by `what`), is held in the result at `into`.
    let fits = |what: String, from: &F::Sort, into: Option<&F::Sort>, role: &str| {
        let into = into.unwrap_or(result_sort);
        (!facts.below(from, into)).then(|| {
            format!(
                "{what}, of sort {}, is {role}, but {} is not {} or a subsort of it",
                facts.render(from),
                facts.render(from),
                facts.render(into)
            )
        })
    };
    for (index, (operand, sort)) in operands.iter().zip(argument_sorts).enumerate() {
        let position = index + 1;
        let argument = || format!("argument {position} of {hook}");
        let reason = match *operand {
            Operand::Read => None,
            Operand::Element => fits(
                argument(),
                sort,
                element.as_ref(),
                "an element of the result",
            ),
            Operand::Key => fits(argument(), sort, key.as_ref(), "a key of the result"),
            Operand::Value => fits(argument(), sort, value.as_ref(), "a value of the result"),
            Operand::Alternative => fits(argument(), sort, None, "a possible result"),
            Operand::Elements(kind) | Operand::Source(kind) => {
                let Some(source) = of_kind(sort, kind) else {
                    return Some(format!(
                        "{}, of sort {}, is no {} sort",
                        argument(),
                        facts.render(sort),
                        kind.noun()
                    ));
                };
                let source_is_result = matches!(operand, Operand::Source(_));
                match source {
                    CollectionShape::List(source_element)
                    | CollectionShape::Set(source_element) => {
                        let role = if source_is_result {
                            "the result"
                        } else {
                            "an element of the result"
                        };
                        let into = if source_is_result {
                            None
                        } else {
                            element.as_ref()
                        };
                        fits(
                            format!("an element of {}", argument()),
                            &source_element,
                            into,
                            role,
                        )
                    }
                    CollectionShape::Map {
                        value: source_value,
                        ..
                    } if source_is_result => fits(
                        format!("a value of {}", argument()),
                        &source_value,
                        None,
                        "the result",
                    ),
                    CollectionShape::Map {
                        key: source_key,
                        value: source_value,
                    } => fits(
                        format!("a key of {}", argument()),
                        &source_key,
                        key.as_ref(),
                        "a key of the result",
                    )
                    .or_else(|| {
                        fits(
                            format!("a value of {}", argument()),
                            &source_value,
                            value.as_ref(),
                            "a value of the result",
                        )
                    }),
                }
            }
            Operand::Keys | Operand::Values => {
                let Some(CollectionShape::Map {
                    key: source_key,
                    value: source_value,
                }) = of_kind(sort, Kind::Map)
                else {
                    return Some(format!(
                        "{}, of sort {}, is no map sort",
                        argument(),
                        facts.render(sort)
                    ));
                };
                let (what, from) = if matches!(operand, Operand::Keys) {
                    ("a key", &source_key)
                } else {
                    ("a value", &source_value)
                };
                fits(
                    format!("{what} of {}", argument()),
                    from,
                    element.as_ref(),
                    "an element of the result",
                )
            }
        };
        if reason.is_some() {
            return reason;
        }
    }
    None
}

fn render(sort: &Sort) -> String {
    match sort {
        Sort::Application { name, arguments } if arguments.is_empty() => name.to_string(),
        Sort::Application { name, arguments } => format!(
            "{name}{{{}}}",
            arguments.iter().map(render).collect::<Vec<_>>().join(", ")
        ),
        Sort::Variable(name) => name.to_string(),
    }
}
