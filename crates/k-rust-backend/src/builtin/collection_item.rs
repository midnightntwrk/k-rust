//! An item or key operand of a `LIST`, `SET` or `MAP` hook read as an element (key) of the
//! collection argument; a responsibility, not an algorithm; no counter of its own, no worklist.
//!
//! A collection of element sort `E` holds its elements as terms of exactly `E`: KORE has no
//! implicit subsorting, so an element of a strict subsort `S` is held as its injection
//! `inj{S, E}(s)` ([`super::ResultCollection`]). A hooked symbol may declare the item it reads
//! (`SET.in`, `LIST.in`, `MAP.in_keys`, the key of `MAP.lookup` and `MAP.lookupOrDefault`) at a
//! sort `I` other than `E`; the application asks about the value the item denotes, so the item
//! and the elements are compared at a common sort:
//!
//! - `I` is `E`: the item as it is.
//! - `I` is a strict subsort of `E`: the item `x` denotes the element `inj{I, E}(x)`.
//!   [`Term::injection`] builds it as stored elements are built, an injection of an injection
//!   collapsing into one from the innermost sort, so that a syntactically equal element is the
//!   same element.
//! - `E` is a strict subsort of `I`: an element `e` is the item `inj{E, I}(e)`. An item that is
//!   itself the injection of a value of `E` or of a subsort of `E` is read as that element of `E`
//!   (it is the injection of that element). Any other item is no stored element written
//!   differently: an element injected into `I` is an injection from `E` or from a sort below it,
//!   so the item can be equal to one only as another value of `I`, and only its absence is
//!   decided, by comparing it with each element injected into `I` ([`Operand::Wider`]).
//! - Otherwise, or when the subsort relation is not known (no sort graph, a sort variable): no
//!   injection is known to relate the item to the elements, and the hook decides nothing about
//!   it ([`Operand::Unrelated`]): it never answers `false`, `\bottom` or a default it cannot justify.
//!
//! Each step is `O(1)` but the wider-sort absence, which compares the item with each element,
//! `O(n)`; equal sorts, the case of every builtin and real-semantics declaration, take the first
//! arm and cost one sort comparison.

use std::borrow::Cow;

use super::{result_collection::below, values_differ};
use crate::{
    matching::SortGraph,
    term::{Sort, Term, TermKind},
};

/// An item operand, read against the elements of a collection.
pub(super) enum Operand<'a> {
    /// The item as a term of the element sort.
    Element(Cow<'a, Term>),
    /// The element sort is a strict subsort of the item's sort, the item's sort is `sort`, and
    /// the item is not the injection of a value of the element sort: it is no element unless it
    /// equals an element injected into `sort` as another value of `sort` ([`absent_above`]).
    Wider { item: &'a Term, sort: Sort },
    /// No injection is known to relate the item to the elements: the hook decides nothing.
    Unrelated,
}

/// `item` read against the elements of a collection whose element (key) sort is `element_sort`.
pub(super) fn read<'a>(
    sorts: Option<&SortGraph>,
    item: &'a Term,
    element_sort: &Sort,
) -> Operand<'a> {
    let item_sort = item.sort();
    if item_sort == *element_sort {
        return Operand::Element(Cow::Borrowed(item));
    }
    if below(sorts, &item_sort, element_sort) {
        return Operand::Element(Cow::Owned(Term::injection(
            item_sort,
            element_sort.clone(),
            item.clone(),
        )));
    }
    if !below(sorts, element_sort, &item_sort) {
        return Operand::Unrelated;
    }
    if let TermKind::Injection { source, term, .. } = item.kind() {
        if source == element_sort {
            return Operand::Element(Cow::Borrowed(term));
        }
        if below(sorts, source, element_sort) {
            return Operand::Element(Cow::Owned(Term::injection(
                source.clone(),
                element_sort.clone(),
                term.clone(),
            )));
        }
    }
    Operand::Wider {
        item,
        sort: item_sort,
    }
}

/// Whether `item`, of `sort` above `element_sort`, differs from each of `elements` (of
/// `element_sort`) injected into `sort`: strict operands make that difference of values
/// (`values_differ`) the item's absence from a collection holding exactly `elements`.
pub(super) fn absent_above<'e>(
    sorts: Option<&SortGraph>,
    item: &Term,
    sort: &Sort,
    element_sort: &Sort,
    mut elements: impl Iterator<Item = &'e Term>,
) -> bool {
    elements.all(|element| {
        values_differ(
            sorts,
            item,
            &Term::injection(element_sort.clone(), sort.clone(), element.clone()),
        )
    })
}
