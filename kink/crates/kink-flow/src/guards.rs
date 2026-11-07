//! Guard outcomes in result records: what a program's baseline run saw of each guard of the
//! specification's authored sentences (k-rust `coverage.guards`, kink-native
//! `TestCoverage::guards`).
//!
//! A record holds, per baseline sentence with a guarded compiled axiom, each axiom's nodes (its
//! written `requires` in preorder: path, shape, and the outcomes the node took where it was
//! reached), its guard outcomes, and its valuation combinations. Atom terms are compact KORE
//! text, as a record's ends are. The `results` rendering reads them ([`crate::results`]).

use k_rust::backend::{AxiomGuardOutput, GuardShapeOutput};
use k_rust::kore::ast::Pattern;
use kink_native::coverage::TestCoverage;
use serde_json::{Value, json};

/// The record value of one axiom's guard outcomes.
fn axiom_value(guard: &AxiomGuardOutput<Pattern>) -> Value {
    let nodes = guard
        .nodes
        .iter()
        .map(|node| {
            let shape = match &node.shape {
                GuardShapeOutput::Connective { connective } => {
                    json!({"node": "connective", "connective": connective})
                }
                GuardShapeOutput::Equals { literal } => {
                    json!({"node": "equals", "literal": literal})
                }
                GuardShapeOutput::Term { term } => {
                    json!({"node": "term", "kore": term.to_string()})
                }
                GuardShapeOutput::Predicate { term } => {
                    json!({"node": "predicate", "kore": term.to_string()})
                }
            };
            json!({"path": node.path, "shape": shape, "reached": node.reached})
        })
        .collect::<Vec<_>>();
    json!({
        "axiom": guard.axiom,
        "nodes": nodes,
        "outcomes": guard.outcomes,
        "combinations": guard.combinations,
        "combinations_truncated": guard.combinations_truncated,
    })
}

/// A record's guard outcomes: per baseline sentence (`module`, `index`), its guarded axioms,
/// in sentence order.
pub(crate) fn record_value(coverage: &TestCoverage) -> Value {
    Value::Array(
        coverage
            .guards
            .iter()
            .map(|(at, guards)| {
                json!({
                    "module": at.module,
                    "index": at.index,
                    "axioms": guards.iter().map(axiom_value).collect::<Vec<_>>(),
                })
            })
            .collect(),
    )
}
