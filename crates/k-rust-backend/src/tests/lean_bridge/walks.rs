//! The macro and k-cell walks of `lean/KRust/TermAttributes.lean` against the Rust:
//! - `firstMacro` against the walk `Term::first_macro_or_alias_symbol` (term.rs), as
//!   `Option<Name>`;
//! - `findK t []` against the cells `find_k_cells` (rule.rs:789-840) pushes into an empty vector,
//!   as `rule_index` calls it (rule.rs:766-777), comparing the whole cell list, not only the
//!   single cell `rule_index` keeps;
//! - `fetchK` against `rule::fetch_k_cell`, the fetch `rule_index` runs when the stored count is
//!   1, on every generated term.

use serde_json::json;

use super::{
    driver::check,
    generators::term,
    term_json::{term_json, terms_json},
};
use crate::rule::{fetch_k_cell, find_k_cells};

/// Coverage is asserted only for runs of at least this many cases.
const COVERAGE_CASES: usize = 1024;

#[test]
fn first_macro_agrees_with_first_macro_or_alias_symbol() {
    let Some(answers) = check("firstMacro", term(), term_json, |term| {
        json!(
            term.first_macro_or_alias_symbol()
                .map(|name| name.to_string())
        )
    }) else {
        return;
    };
    let found = answers.iter().filter(|answer| !answer.is_null()).count();
    eprintln!(
        "lean bridge: firstMacro found a macro in {found} of {} cases",
        answers.len()
    );
    if answers.len() >= COVERAGE_CASES {
        assert!(
            found > 0 && found < answers.len(),
            "the generator should reach terms with and without a macro"
        );
    }
}

#[test]
fn find_k_agrees_with_find_k_cells() {
    let Some(answers) = check("findK", term(), term_json, |term| {
        let mut cells = Vec::with_capacity(2);
        find_k_cells(term, &mut cells);
        terms_json(cells)
    }) else {
        return;
    };
    let mut by_length = [0usize; 3];
    for answer in &answers {
        let length = answer.as_array().map_or(0, Vec::len);
        by_length[length.min(2)] += 1;
    }
    eprintln!(
        "lean bridge: findK returned 0, 1 and 2 cells in {by_length:?} of {} cases",
        answers.len()
    );
    if answers.len() >= COVERAGE_CASES {
        assert!(
            by_length.iter().all(|&count| count > 0),
            "the generator should reach terms with no, one and several k cells"
        );
    }
}

#[test]
fn fetch_k_agrees_with_fetch_k_cell() {
    let Some(answers) = check("fetchK", term(), term_json, |term| {
        fetch_k_cell(term).map_or(serde_json::Value::Null, term_json)
    }) else {
        return;
    };
    let found = answers.iter().filter(|answer| !answer.is_null()).count();
    eprintln!(
        "lean bridge: fetchK found a cell in {found} of {} cases",
        answers.len()
    );
    if answers.len() >= COVERAGE_CASES {
        assert!(
            found > 0 && found < answers.len(),
            "the generator should reach terms with and without a k cell"
        );
    }
}
