//! The collection a `LIST`, `SET` or `MAP` hook builds its result in; a responsibility, not an
//! algorithm; no counter of its own, no worklist.
//!
//! A hooked symbol `f : S1 ... Sn -> S` denotes a value of `S`, whatever computes it, and KORE
//! has no implicit subsorting: a value of a collection sort `S` is built from `S`'s own unit,
//! element and concatenation symbols and holds elements of exactly `S`'s element (key, value)
//! sorts, an element of a strict subsort `Sub` being written `inj{Sub, E}(e)`. The description of
//! `S` is built once, from its declaration, and the load gives it to every hooked symbol whose
//! result sort is `S` (`SymbolAttributes::result_collection`). Every collection a hook returns
//! is built here, in that description:
//!
//! - an element whose sort is the result's element sort is kept as it is, so a hook that
//!   transforms a collection of the result sort copies nothing more than it did;
//! - an element of a strict subsort of it is injected;
//! - an element of any other sort, a result sort that is no collection of the hook's kind, or an
//!   opaque rest of another sort than the result's leaves the application unevaluated: the
//!   declaration gives it no value this evaluator can build. A loaded definition holds no
//!   declaration under which an element's sort or the result's kind cannot fit
//!   ([`super::hook_signature`] rejects it), so there only an opaque rest declines here.

use std::{borrow::Cow, sync::Arc};

use crate::{
    matching::SortGraph,
    term::{CollectionMetadata, ListDefinition, MapDefinition, Name, SetDefinition, Sort, Term},
};

/// What the applied symbol declares its result to be.
#[derive(Clone, Copy, Debug)]
enum Declared<'a> {
    /// No symbol is applied (`builtin::evaluate_hook`), so no result sort is declared. A hook
    /// that transforms a collection argument builds its result in that argument's collection,
    /// which is the hook's own signature on the builtin sorts; a hook that introduces a
    /// collection has none to build in and declines.
    Nothing,
    /// The symbol's result sort: its collection, or `None` for a sort that is no collection
    /// sort, which no collection hook builds a value of.
    Sort(Option<&'a CollectionMetadata>),
}

/// The collection a hook's result is built in, and the subsort relation that decides which
/// elements it may hold.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ResultCollection<'a> {
    declared: Declared<'a>,
    sorts: Option<&'a SortGraph>,
}

impl<'a> ResultCollection<'a> {
    /// The result of an application of a symbol whose result sort's collection is `collection`
    /// (`None`: its result sort is no collection sort).
    pub(crate) const fn declared(
        collection: Option<&'a CollectionMetadata>,
        sorts: Option<&'a SortGraph>,
    ) -> Self {
        Self {
            declared: Declared::Sort(collection),
            sorts,
        }
    }

    /// The result of a hook applied without a symbol.
    pub(crate) const fn undeclared(sorts: Option<&'a SortGraph>) -> Self {
        Self {
            declared: Declared::Nothing,
            sorts,
        }
    }

    /// A list result; `source` is the collection argument the hook transforms, if it does.
    pub(super) fn list(self, source: Option<&Arc<ListDefinition>>) -> Option<ListResult<'a>> {
        let definition = match self.declared {
            Declared::Nothing => source?.clone(),
            Declared::Sort(Some(CollectionMetadata::List(definition))) => definition.clone(),
            Declared::Sort(_) => return None,
        };
        Some(ListResult {
            elements: Elements {
                definition,
                sorts: self.sorts,
            },
        })
    }

    /// A set result; `source` is the collection argument the hook transforms, if it does.
    pub(super) fn set(self, source: Option<&Arc<SetDefinition>>) -> Option<SetResult<'a>> {
        let definition = match self.declared {
            Declared::Nothing => source?.clone(),
            Declared::Sort(Some(CollectionMetadata::Set(definition))) => definition.clone(),
            Declared::Sort(_) => return None,
        };
        Some(SetResult {
            elements: Elements {
                definition,
                sorts: self.sorts,
            },
        })
    }

    /// A map result; `source` is the collection argument the hook transforms, if it does.
    pub(super) fn map(self, source: Option<&Arc<MapDefinition>>) -> Option<MapResult<'a>> {
        let definition = match self.declared {
            Declared::Nothing => source?.clone(),
            Declared::Sort(Some(CollectionMetadata::Map(definition))) => definition.clone(),
            Declared::Sort(_) => return None,
        };
        Some(MapResult {
            definition,
            sorts: self.sorts,
        })
    }
}

/// `element`, of sort `from`, as a term of sort `into`: itself when the sorts are equal, its
/// injection when `from` is a strict subsort of `into`, and `None` otherwise.
fn convert(sorts: Option<&SortGraph>, element: Term, from: &Sort, into: &Name) -> Option<Term> {
    let into = Sort::simple(into.clone());
    if *from == into {
        return Some(element);
    }
    below(sorts, from, &into).then(|| Term::injection(from.clone(), into, element))
}

/// `elements`, all of sort `from`, as terms of sort `into`: borrowed when the sorts are equal,
/// so that a hook transforming a collection of the result sort copies nothing for it.
fn convert_all<'e>(
    sorts: Option<&SortGraph>,
    elements: &'e [Term],
    from: &Name,
    into: &Name,
) -> Option<Cow<'e, [Term]>> {
    if from == into {
        return Some(Cow::Borrowed(elements));
    }
    let (from, into) = (Sort::simple(from.clone()), Sort::simple(into.clone()));
    below(sorts, &from, &into).then(|| {
        Cow::Owned(
            elements
                .iter()
                .map(|element| Term::injection(from.clone(), into.clone(), element.clone()))
                .collect(),
        )
    })
}

fn below(sorts: Option<&SortGraph>, sub: &Sort, sup: &Sort) -> bool {
    sorts.is_some_and(|sorts| matches!(sorts.check_subsort(sub, sup), Ok(true)))
}

/// Whether an opaque rest may stand in the result: only a value of the result sort can.
fn fits(rest: &Term, collection_sort: &Name) -> bool {
    rest.sort() == Sort::simple(collection_sort.clone())
}

/// The elements of a list or set result.
struct Elements<'a> {
    definition: Arc<ListDefinition>,
    sorts: Option<&'a SortGraph>,
}

impl Elements<'_> {
    fn element(&self, element: Term) -> Option<Term> {
        let from = element.sort();
        convert(self.sorts, element, &from, &self.definition.element_sort)
    }

    fn elements<'e>(&self, elements: &'e [Term], from: &Name) -> Option<Cow<'e, [Term]>> {
        convert_all(self.sorts, elements, from, &self.definition.element_sort)
    }

    fn owned_elements(&self, elements: Vec<Term>, from: &Name) -> Option<Vec<Term>> {
        if *from == self.definition.element_sort {
            return Some(elements);
        }
        Some(self.elements(&elements, from)?.into_owned())
    }
}

/// A list result being built in the declared result sort.
pub(super) struct ListResult<'a> {
    elements: Elements<'a>,
}

impl ListResult<'_> {
    /// Elements of sort `from` the hook computed, as elements of the result.
    pub(super) fn owned_elements(&self, elements: Vec<Term>, from: &Name) -> Option<Vec<Term>> {
        self.elements.owned_elements(elements, from)
    }

    /// An element argument of the hook, as an element of the result.
    pub(super) fn element(&self, element: Term) -> Option<Term> {
        self.elements.element(element)
    }

    /// The elements of a list or set argument whose element sort is `from`, as elements of the
    /// result.
    pub(super) fn elements<'e>(
        &self,
        elements: &'e [Term],
        from: &Name,
    ) -> Option<Cow<'e, [Term]>> {
        self.elements.elements(elements, from)
    }

    /// The list of `heads`, and of an opaque middle and its `tails` when the middle is a value
    /// of the result sort; the elements are already the result's (`element`, `elements`).
    pub(super) fn build(self, heads: Vec<Term>, rest: Option<(Term, Vec<Term>)>) -> Option<Term> {
        let definition = self.elements.definition;
        if let Some((middle, _)) = &rest
            && !fits(middle, &definition.list_sort)
        {
            return None;
        }
        Some(Term::list(definition, heads, rest))
    }
}

/// A set result being built in the declared result sort.
pub(super) struct SetResult<'a> {
    elements: Elements<'a>,
}

impl SetResult<'_> {
    /// Elements of sort `from` the hook computed, as elements of the result.
    pub(super) fn owned_elements(&self, elements: Vec<Term>, from: &Name) -> Option<Vec<Term>> {
        self.elements.owned_elements(elements, from)
    }

    /// An element argument of the hook, as an element of the result.
    pub(super) fn element(&self, element: Term) -> Option<Term> {
        self.elements.element(element)
    }

    /// The elements of a list or set argument (the keys of a map argument) whose element sort is
    /// `from`, as elements of the result.
    pub(super) fn elements<'e>(
        &self,
        elements: &'e [Term],
        from: &Name,
    ) -> Option<Cow<'e, [Term]>> {
        self.elements.elements(elements, from)
    }

    /// The set of `elements`, and of an opaque `rest` when it is a value of the result sort;
    /// the elements are already the result's (`element`, `elements`).
    pub(super) fn build(self, elements: Vec<Term>, rest: Option<Term>) -> Option<Term> {
        let definition = self.elements.definition;
        if rest
            .as_ref()
            .is_some_and(|rest| !fits(rest, &definition.list_sort))
        {
            return None;
        }
        Some(Term::set(definition, elements, rest))
    }
}

/// A map result being built in the declared result sort.
pub(super) struct MapResult<'a> {
    definition: Arc<MapDefinition>,
    sorts: Option<&'a SortGraph>,
}

impl MapResult<'_> {
    /// A key argument of the hook, as a key of the result.
    pub(super) fn key(&self, key: Term) -> Option<Term> {
        let from = key.sort();
        convert(self.sorts, key, &from, &self.definition.key_sort)
    }

    /// A value argument of the hook, as a value of the result.
    pub(super) fn value(&self, value: Term) -> Option<Term> {
        let from = value.sort();
        convert(self.sorts, value, &from, &self.definition.value_sort)
    }

    /// The entries of a map argument of collection `from`, as entries of the result.
    pub(super) fn entries<'e>(
        &self,
        entries: &'e [(Term, Term)],
        from: &MapDefinition,
    ) -> Option<Cow<'e, [(Term, Term)]>> {
        if from.key_sort == self.definition.key_sort
            && from.value_sort == self.definition.value_sort
        {
            return Some(Cow::Borrowed(entries));
        }
        let key_sort = Sort::simple(from.key_sort.clone());
        let value_sort = Sort::simple(from.value_sort.clone());
        entries
            .iter()
            .map(|(key, value)| {
                Some((
                    convert(
                        self.sorts,
                        key.clone(),
                        &key_sort,
                        &self.definition.key_sort,
                    )?,
                    convert(
                        self.sorts,
                        value.clone(),
                        &value_sort,
                        &self.definition.value_sort,
                    )?,
                ))
            })
            .collect::<Option<Vec<_>>>()
            .map(Cow::Owned)
    }

    /// The map of `entries`, and of an opaque `rest` when it is a value of the result sort; the
    /// entries are already the result's (`key`, `value`, `entries`).
    pub(super) fn build(self, entries: Vec<(Term, Term)>, rest: Option<Term>) -> Option<Term> {
        if rest
            .as_ref()
            .is_some_and(|rest| !fits(rest, &self.definition.map_sort))
        {
            return None;
        }
        Some(Term::map(self.definition, entries, rest))
    }

    /// A whole map argument returned as the result: itself when it is a value of the result
    /// sort, else its entries rebuilt in the result's collection.
    pub(super) fn adopt(self, map: &Term) -> Option<Term> {
        let crate::term::TermKind::Map {
            definition,
            entries,
            rest,
        } = map.kind()
        else {
            return fits(map, &self.definition.map_sort).then(|| map.clone());
        };
        if *definition == self.definition {
            return Some(map.clone());
        }
        let entries = self.entries(entries, definition)?.into_owned();
        self.build(entries, rest.clone())
    }
}
