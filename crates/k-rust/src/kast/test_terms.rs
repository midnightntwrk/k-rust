//! Test support: random terms holding every constructor, and the nodes of a term with their
//! destination paths.
//!
//! Two conventions number the nodes of a sentence's terms: term-metadata addresses take nodes in
//! preorder, and destination paths take one step per level. Each must hold on every constructor,
//! so the properties that check them draw terms from [`every_constructor`], and compare against
//! [`positions`] and [`paired`]. A destination path's steps are those of [`Term::children`], the
//! one enumeration of a node's children in step order, whose order its own unit test states
//! against the constructors' fields; [`positions`] lists a term's nodes through it, so a
//! property compares the paths a walk records with the paths that name the nodes. [`paired`]
//! follows the constructors' fields rather than any walk.

use proptest::prelude::*;

use super::{Label, Sort, Term, TermMetadata};

/// Random terms of up to four levels in which every constructor occurs: nullary applications,
/// variables, tokens and injected labels at the leaves; rewrites, aliases, sequences and
/// applications of up to three arguments above them.
pub(crate) fn every_constructor() -> impl Strategy<Value = Term> {
    let leaf = (0_u8..4, 0_u8..3).prop_map(|(kind, name)| match kind {
        0 => Term::apply(format!("c{name}"), Vec::new()),
        1 => Term::variable(format!("X{name}")),
        2 => Term::Token {
            token: name.to_string(),
            sort: Sort::new("Int"),
        },
        _ => Term::InjectedLabel(Label::new(format!("l{name}"))),
    });
    leaf.prop_recursive(3, 32, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(left, right)| Term::Rewrite {
                left: Box::new(left),
                right: Box::new(right),
            }),
            (inner.clone(), inner.clone()).prop_map(|(pattern, alias)| Term::As {
                pattern: Box::new(pattern),
                alias: Box::new(alias),
            }),
            prop::collection::vec(inner.clone(), 0..4).prop_map(Term::Sequence),
            (0_u8..3, prop::collection::vec(inner, 0..4))
                .prop_map(|(name, arguments)| Term::apply(format!("n{name}"), arguments)),
        ]
    })
}

/// `term` rebuilt with the metadata `metadata` returns for each node attached to it (none where it
/// returns `None`); the nodes are asked in an order of this function's own.
pub(crate) fn decorated(term: &Term, metadata: &mut impl FnMut() -> Option<TermMetadata>) -> Term {
    let bare = match term.unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(decorated(left, metadata)),
            right: Box::new(decorated(right, metadata)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(decorated(pattern, metadata)),
            alias: Box::new(decorated(alias, metadata)),
        },
        Term::Sequence(items) => {
            Term::Sequence(items.iter().map(|item| decorated(item, metadata)).collect())
        }
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| decorated(argument, metadata))
                .collect(),
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
            leaf.clone()
        }
        Term::Annotated { .. } => unreachable!("unannotated strips annotations"),
    };
    match metadata() {
        Some(metadata) => bare.with_metadata(metadata),
        None => bare,
    }
}

/// Every node of `term` (its annotation, when it has one) with the steps that lead to it from
/// `term`.
pub(crate) fn positions(term: &Term) -> Vec<(Vec<u32>, &Term)> {
    let mut found = Vec::new();
    let mut pending = vec![(Vec::new(), term)];
    while let Some((steps, node)) = pending.pop() {
        for (step, child) in (0..).zip(node.children()) {
            let mut child_steps = steps.clone();
            child_steps.push(step);
            pending.push((child_steps, child));
        }
        found.push((steps, node));
    }
    found
}

/// The corresponding nodes of two terms of the same shape, each with its annotation; panics where
/// the shapes differ. The pairing follows the constructors' fields, so it holds whatever order a
/// walk visits them in.
pub(crate) fn paired<'a>(left: &'a Term, right: &'a Term) -> Vec<(&'a Term, &'a Term)> {
    let mut pairs = Vec::new();
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        pairs.push((left, right));
        match (left.unannotated(), right.unannotated()) {
            (
                Term::Rewrite {
                    left: left_left,
                    right: left_right,
                },
                Term::Rewrite {
                    left: right_left,
                    right: right_right,
                },
            ) => pending.extend([(&**left_left, &**right_left), (left_right, right_right)]),
            (
                Term::As {
                    pattern: left_pattern,
                    alias: left_alias,
                },
                Term::As {
                    pattern: right_pattern,
                    alias: right_alias,
                },
            ) => pending.extend([
                (&**left_pattern, &**right_pattern),
                (left_alias, right_alias),
            ]),
            (Term::Sequence(left_items), Term::Sequence(right_items))
            | (
                Term::Apply {
                    arguments: left_items,
                    ..
                },
                Term::Apply {
                    arguments: right_items,
                    ..
                },
            ) => {
                assert_eq!(left_items.len(), right_items.len(), "{left:?} / {right:?}");
                pending.extend(left_items.iter().zip(right_items));
            }
            (Term::InjectedLabel(left_label), Term::InjectedLabel(right_label)) => {
                assert_eq!(left_label, right_label);
            }
            (left @ Term::Variable { .. }, right @ Term::Variable { .. })
            | (left @ Term::Token { .. }, right @ Term::Token { .. }) => assert_eq!(left, right),
            (left, right) => panic!("{left:?} and {right:?} differ in shape"),
        }
    }
    pairs
}

/// Every constructor [`every_constructor`]'s documentation names occurs in its terms: nullary
/// applications, variables, tokens and injected labels, and rewrites, aliases, sequences and
/// applications with arguments.
#[test]
fn every_constructor_produces_every_constructor() {
    use std::collections::BTreeMap;

    use proptest::{
        strategy::ValueTree,
        test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
    };
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let strategy = every_constructor();
    let mut found = BTreeMap::<&str, usize>::new();
    for _ in 0..256 {
        let term = strategy.new_tree(&mut runner).expect("a case").current();
        for (_, node) in positions(&term) {
            let constructor = match node.unannotated() {
                Term::Apply { arguments, .. } if arguments.is_empty() => "nullary application",
                Term::Apply { .. } => "application with arguments",
                Term::Variable { .. } => "variable",
                Term::Token { .. } => "token",
                Term::InjectedLabel(_) => "injected label",
                Term::Rewrite { .. } => "rewrite",
                Term::As { .. } => "alias",
                Term::Sequence(_) => "sequence",
                Term::Annotated { .. } => unreachable!("unannotated strips annotations"),
            };
            *found.entry(constructor).or_default() += 1;
        }
    }
    for constructor in [
        "nullary application",
        "application with arguments",
        "variable",
        "token",
        "injected label",
        "rewrite",
        "alias",
        "sequence",
    ] {
        assert!(
            found.contains_key(constructor),
            "no {constructor}: {found:?}"
        );
    }
}
