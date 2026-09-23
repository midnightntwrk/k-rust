//! The construction-time attributes of term.rs against their definitions in
//! `lean/KRust/TermAttributes.lean`, at every subterm of terms built by the public constructors:
//! - `ceilFree` against the stored `TermAttributes::ceil_free` (term.rs `ceil_free`);
//! - `hasMacro` against the stored `TermAttributes::has_macro_or_alias` (term.rs
//!   `has_macro_or_alias`);
//! - `kCells` against the stored `TermAttributes::k_cells` (term.rs `k_cells`).
//!
//! The proofs (`ceilFree_sound`, `hasMacro_iff`, `kCells_eq`, `rule_index_same`) are about the
//! Lean functions; these tests check that each stored value is that function, so the proofs
//! apply to the shortcuts that read the stored values.
//!
//! Each case sends every subterm of one generated term, in preorder, so that a node deep inside a
//! term whose root answer does not depend on it is still compared.

use lean_conformance::check;
use serde_json::{Value, json};

use super::{
    generators::{term, term_with_ground_keys},
    term_json::terms_json,
};
use crate::term::{Term, TermKind};

/// Coverage is asserted only for runs of at least this many cases.
const COVERAGE_CASES: usize = 1024;

/// Every subterm of `term`, itself first, in the order of `Term::visit_symbols`.
fn subterms(term: &Term) -> Vec<Term> {
    fn visit(term: &Term, out: &mut Vec<Term>) {
        out.push(term.clone());
        match term.kind() {
            TermKind::And(left, right) => {
                visit(left, out);
                visit(right, out);
            }
            TermKind::Application { arguments, .. } => {
                arguments.iter().for_each(|argument| visit(argument, out));
            }
            TermKind::Injection { term, .. } => visit(term, out),
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries {
                    visit(key, out);
                    visit(value, out);
                }
                rest.iter().for_each(|rest| visit(rest, out));
            }
            TermKind::List { heads, rest, .. } => {
                heads.iter().for_each(|head| visit(head, out));
                if let Some((middle, tails)) = rest {
                    visit(middle, out);
                    tails.iter().for_each(|tail| visit(tail, out));
                }
            }
            TermKind::Set { elements, rest, .. } => {
                elements.iter().for_each(|element| visit(element, out));
                rest.iter().for_each(|rest| visit(rest, out));
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }
    let mut out = Vec::new();
    visit(term, &mut out);
    out
}

/// Check `model` against `stored` at every subterm, and return every compared value, or `None`
/// when the bridge is switched off.
fn check_every_subterm(
    model: &str,
    strategy: impl proptest::strategy::Strategy<Value = Term>,
    stored: impl Fn(&Term) -> Value,
) -> Option<Vec<Value>> {
    let answers = check(
        model,
        strategy,
        |term| terms_json(&subterms(term)),
        |term| Value::Array(subterms(term).iter().map(&stored).collect()),
    )?;
    let values = answers
        .into_iter()
        .flat_map(|answer| match answer {
            Value::Array(values) => values,
            other => vec![other],
        })
        .collect::<Vec<_>>();
    eprintln!("lean bridge: model {model} at {} subterms", values.len());
    Some(values)
}

/// With enough cases, every value in `expected` occurs among `values`.
fn assert_reached(model: &str, values: &[Value], expected: &[Value]) {
    if values.len() < COVERAGE_CASES {
        return;
    }
    for value in expected {
        let count = values.iter().filter(|seen| *seen == value).count();
        eprintln!("lean bridge: model {model} answered {value} at {count} subterms");
        assert!(
            count > 0,
            "the generator should reach subterms where {model} is {value}"
        );
    }
}

#[test]
fn ceil_free_agrees_with_ceil_free_model() {
    let Some(values) = check_every_subterm("ceilFree", term_with_ground_keys(), |term| {
        json!(term.attributes().ceil_free())
    }) else {
        return;
    };
    assert_reached("ceilFree", &values, &[json!(true), json!(false)]);
}

#[test]
fn has_macro_or_alias_agrees_with_has_macro_model() {
    let Some(values) = check_every_subterm("hasMacro", term(), |term| {
        json!(term.attributes().has_macro_or_alias())
    }) else {
        return;
    };
    assert_reached("hasMacro", &values, &[json!(true), json!(false)]);
}

#[test]
fn k_cells_agrees_with_k_cells_model() {
    let Some(values) =
        check_every_subterm("kCells", term(), |term| json!(term.attributes().k_cells()))
    else {
        return;
    };
    assert_reached("kCells", &values, &[json!(0), json!(1), json!(2)]);
}
