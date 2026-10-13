//! Terms deeper than the thread they are dropped on (`docs/backend-port.md`, "Stack bounds").
//!
//! A failure here is a stack overflow, which aborts the process; these tests live in their own
//! binary so that the abort takes down only this file's tests.

use std::sync::Arc;

use k_rust_backend::term::{CollectionSymbols, ListDefinition, MapDefinition, Sort, Symbol, Term};

/// The stack of the thread each test drops on: the glue of a term a few thousand levels deep
/// overflows it in every build.
const SMALL_STACK: usize = 256 << 10;

/// The levels of the deep terms: execution builds terms this deep in a few seconds.
const LEVELS: usize = 100_000;

fn collection_symbols(prefix: &str) -> CollectionSymbols {
    CollectionSymbols {
        unit: format!("{prefix}unit").into(),
        element: format!("{prefix}element").into(),
        concat: format!("{prefix}concat").into(),
    }
}

fn on_small_thread(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(SMALL_STACK)
        .spawn(work)
        .expect("the worker should spawn")
        .join()
        .expect("the worker should not panic");
}

/// A term [`LEVELS`] deep, nested in turn through every kind of node that holds a subterm (an
/// application argument, both sides of `\and`, an injection, a map key and value, a list head
/// and a set element), with a shared leaf beside the nested subterm at each level.
fn mixed_deep_term() -> Term {
    let sort = Sort::simple("SortS");
    let leaf = Term::raw_domain_value(sort.clone(), "0");
    let wrap = Arc::new(Symbol::constructor(
        "wrap",
        vec![sort.clone(), sort.clone()],
        sort.clone(),
    ));
    let map = Arc::new(MapDefinition {
        symbols: collection_symbols("Map"),
        key_sort: Sort::simple("SortS"),
        value_sort: Sort::simple("SortS"),
        map_sort: "SortMap".into(),
    });
    let list = Arc::new(ListDefinition {
        symbols: collection_symbols("List"),
        element_sort: Sort::simple("SortS"),
        list_sort: "SortList".into(),
    });
    let set = Arc::new(ListDefinition {
        symbols: collection_symbols("Set"),
        element_sort: Sort::simple("SortS"),
        list_sort: "SortSet".into(),
    });
    let mut term = leaf.clone();
    for level in 0..LEVELS {
        let (deep, leaf) = (term, leaf.clone());
        term = match level % 7 {
            0 => Term::application(wrap.clone(), Vec::new(), vec![leaf, deep]),
            1 => Term::and(deep, leaf),
            2 => Term::and(leaf, deep),
            3 => Term::injection(Sort::simple("SortS"), Sort::simple("SortT"), deep),
            4 => Term::map(map.clone(), vec![(leaf, deep)], None),
            5 => Term::list(list.clone(), vec![leaf, deep], None),
            _ => Term::set(set.clone(), vec![deep], None),
        };
    }
    term
}

/// Dropping the last handle of a term far deeper than the thread frees it without overflowing.
#[test]
fn a_deep_term_drops_on_a_small_thread() {
    on_small_thread(|| drop(mixed_deep_term()));
}

/// A deep term whose upper half is shared with a second handle: dropping the first handle frees
/// only what it alone owns, and dropping the second then frees the rest, each on a small thread.
#[test]
fn a_partly_shared_deep_term_drops_on_a_small_thread() {
    on_small_thread(|| {
        let sort = Sort::simple("SortS");
        let wrap = Arc::new(Symbol::constructor(
            "wrap",
            vec![sort.clone()],
            sort.clone(),
        ));
        let mut term = Term::raw_domain_value(sort, "0");
        let mut kept = None;
        for level in 0..LEVELS {
            term = Term::application(wrap.clone(), Vec::new(), vec![term]);
            if level == LEVELS / 2 {
                kept = Some(term.clone());
            }
        }
        drop(term);
        drop(kept);
    });
}

/// A deep term that a thread-local of the thread holds is freed by that thread-local's destructor
/// at the thread's exit, whether or not the leaf a drop leaves in the handles it takes apart is
/// still there: here that leaf is made before the holder is filled, so it is destroyed first
/// where destructors run in the reverse order of their registration.
#[test]
fn a_deep_term_held_by_a_thread_local_drops_at_the_thread_exit() {
    std::thread_local! {
        static HELD: std::cell::RefCell<Option<Term>> = const { std::cell::RefCell::new(None) };
    }
    on_small_thread(|| {
        HELD.with(|held| held.borrow_mut().take());
        drop(mixed_deep_term());
        HELD.with(|held| *held.borrow_mut() = Some(mixed_deep_term()));
    });
}
