//! The construction-time attributes of term.rs against their definitions in
//! `lean/KRust/TermAttributes.lean`, at every subterm of terms built by the public constructors:
//! - `ceilFree` against the stored `TermAttributes::ceil_free` (term.rs `ceil_free`), as a
//!   Boolean. The proof `ceilFree_sound` is about the Lean function; this test checks that the
//!   stored bit is that function, so the proof applies to the shortcut in
//!   `definedness::ceil_term_recursive`.
//!
//! Each case sends every subterm of one generated term, in preorder, so that a node deep inside a
//! term whose root answer does not depend on it is still compared.

use serde_json::{Value, json};

use super::{driver::check, generators::term_with_ground_keys, term_json::terms_json};
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

#[test]
fn ceil_free_agrees_with_ceil_free_model() {
    let Some(answers) = check(
        "ceilFree",
        term_with_ground_keys(),
        |term| terms_json(&subterms(term)),
        |term| {
            json!(
                subterms(term)
                    .iter()
                    .map(|subterm| subterm.attributes().ceil_free())
                    .collect::<Vec<_>>()
            )
        },
    ) else {
        return;
    };
    let flags = answers
        .iter()
        .flat_map(|answer| answer.as_array().into_iter().flatten())
        .collect::<Vec<&Value>>();
    let free = flags.iter().filter(|flag| ***flag == json!(true)).count();
    eprintln!(
        "lean bridge: ceilFree true at {free} of {} subterms in {} cases",
        flags.len(),
        answers.len()
    );
    if answers.len() >= COVERAGE_CASES {
        assert!(
            free > 0 && free < flags.len(),
            "the generator should reach subterms with and without the attribute"
        );
    }
}
