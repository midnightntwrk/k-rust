//! The ordered, versioned catalogue of declarative mutation operators.

use crate::{Action, Clause, OperatorSpec};
use k_rust::kast::Sort;

const RELATIONS: [&str; 6] = [
    "_<Int_", "_<=Int_", "_>Int_", "_>=Int_", "_==Int_", "_=/=Int_",
];
const ARITHMETIC: [&str; 5] = ["_+Int_", "_-Int_", "_*Int_", "_/Int_", "_%Int_"];

/// Catalogue v1 in table order, with ordered replacement pairs in operand order.
///
/// Each spec has one variant and uses the `each` policy.
#[must_use]
pub fn catalogue_v1() -> Vec<OperatorSpec> {
    let mut specs = Vec::new();
    for (id, token) in [("cond-true", "true"), ("cond-false", "false")] {
        specs.push(spec(
            id,
            "1",
            vec![
                Clause::Path(vec![1]),
                Clause::NotToken {
                    token: token.to_owned(),
                    sort: Sort::new("Bool"),
                },
            ],
            Action::ReplaceWithToken {
                token: token.to_owned(),
                sort: Sort::new("Bool"),
            },
        ));
    }
    specs.push(spec(
        "cond-negate",
        "1",
        vec![
            Clause::Path(vec![1]),
            Clause::NotToken {
                token: "true".to_owned(),
                sort: Sort::new("Bool"),
            },
        ],
        Action::Wrap {
            label: "notBool_".to_owned(),
        },
    ));
    specs.push(spec(
        "not-unwrap",
        "1",
        vec![Clause::Head {
            label: "notBool_".to_owned(),
        }],
        Action::Unwrap { argument: 0 },
    ));
    for (id, labels) in [
        ("ror", RELATIONS.as_slice()),
        ("aor", ARITHMETIC.as_slice()),
        ("lcr", ["_andBool_", "_orBool_"].as_slice()),
        ("eqk", ["_==K_", "_=/=K_"].as_slice()),
    ] {
        for from in labels {
            for to in labels {
                if from != to {
                    specs.push(spec(
                        id,
                        &format!("{from}->{to}"),
                        vec![Clause::Head {
                            label: (*from).to_owned(),
                        }],
                        Action::ReplaceHead {
                            to: (*to).to_owned(),
                        },
                    ));
                }
            }
        }
    }
    for (variant, offset) in [("+1", 1), ("-1", -1)] {
        specs.push(spec(
            "int-literal",
            variant,
            vec![Clause::TokenOfSort {
                sort: Sort::new("Int"),
            }],
            Action::IntOffset(offset),
        ));
    }
    for (id, key) in [("drop-owise", "owise"), ("drop-priority", "priority")] {
        specs.push(spec(
            id,
            "1",
            vec![
                Clause::Path(vec![0]),
                Clause::RuleAttribute {
                    key: key.to_owned(),
                    present: true,
                },
            ],
            Action::RemoveAttribute {
                key: key.to_owned(),
            },
        ));
    }
    specs.push(spec(
        "delete-rule",
        "1",
        vec![Clause::Path(vec![0])],
        Action::DeleteRule,
    ));
    specs
}

fn spec(id: &str, variant: &str, selector: Vec<Clause>, action: Action) -> OperatorSpec {
    OperatorSpec::new(id, variant, 1, selector, action).expect("catalogue v1 specs are valid")
}
