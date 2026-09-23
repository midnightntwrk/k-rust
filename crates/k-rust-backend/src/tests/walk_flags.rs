//! OT-02: the stored `has_macro_or_alias` and `k_cells` attributes against the walks they
//! replace, over terms of every `TermKind` built by the public constructors
//! (`lean_bridge::generators::term`).
//!
//! - `has_macro_or_alias` is true exactly when `Term::first_macro_or_alias_symbol` finds a symbol,
//!   and `Term::macro_or_alias_symbol`, which reads the flag, returns what the walk returns
//!   (`hasMacro_iff`, `macro_shortcut_eq` of `lean/KRust/TermAttributes.lean`);
//! - `k_cells` is the number of cells `find_k_cells` collects (it stops at two), `fetch_k_cell`
//!   returns the first of them, and so the cell `rule_index` keys on, fetched only when the count
//!   is 1, is the one `find_k_cells` left alone in its vector (`kCells_eq`, `fetchK_eq`,
//!   `rule_index_same`). Cells are compared by allocation, so the fetch must return the same
//!   subterm, not only an equal one.

use proptest::{
    strategy::{Strategy, ValueTree},
    test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
};

use super::lean_bridge::generators::term;
use crate::{
    rule::{fetch_k_cell, find_k_cells},
    term::Term,
};

const CASES: usize = 4096;

fn same_cell(left: Option<&Term>, right: Option<&Term>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => left.ptr_eq(right),
        _ => false,
    }
}

#[test]
fn walk_flags_equal_the_walks() {
    let strategy = term();
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let mut macros = [0usize; 2];
    let mut cells_seen = [0usize; 3];
    for case in 0..CASES {
        let term = strategy.new_tree(&mut runner).expect("a case").current();
        let attributes = term.attributes();

        let walked = term.first_macro_or_alias_symbol();
        assert_eq!(
            attributes.has_macro_or_alias(),
            walked.is_some(),
            "case {case}: has_macro_or_alias differs from the walk on {term:?}"
        );
        assert_eq!(
            term.macro_or_alias_symbol(),
            walked,
            "case {case}: macro_or_alias_symbol differs from the walk on {term:?}"
        );
        macros[usize::from(walked.is_some())] += 1;

        let mut cells = Vec::with_capacity(2);
        find_k_cells(&term, &mut cells);
        assert_eq!(
            usize::from(attributes.k_cells()),
            cells.len(),
            "case {case}: k_cells differs from find_k_cells on {term:?}"
        );
        assert!(
            same_cell(fetch_k_cell(&term), cells.first().copied()),
            "case {case}: fetch_k_cell is not the first cell find_k_cells collects in {term:?}"
        );
        let indexed = match attributes.k_cells() {
            1 => fetch_k_cell(&term),
            _ => None,
        };
        let walked_cell = match cells.as_slice() {
            [cell] => Some(*cell),
            _ => None,
        };
        assert!(
            same_cell(indexed, walked_cell),
            "case {case}: the indexed cell differs from the walk's on {term:?}"
        );
        cells_seen[cells.len()] += 1;
    }
    eprintln!("macro found [no, yes]: {macros:?}; k cells [0, 1, 2]: {cells_seen:?}");
    assert!(
        macros.iter().chain(&cells_seen).all(|&count| count > 0),
        "the generator should reach terms with and without a macro, and with 0, 1 and 2 cells"
    );
}
