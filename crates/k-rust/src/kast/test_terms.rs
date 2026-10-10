//! Test support: random terms holding every constructor, and a statement of a term's child steps
//! written independently of the walks under test.
//!
//! Two conventions number the nodes of a sentence's terms: term-metadata addresses take nodes in
//! preorder, and destination paths take one step per level. Each must hold on every constructor,
//! so the properties that check them draw terms from [`every_constructor`], and compare against
//! [`positions`] and [`paired`], which follow the specification below rather than the code under
//! test: a `Rewrite`'s child 0 is its left side and child 1 its right side, an `As`'s child 0 is
//! its pattern and child 1 its alias, and a sequence's or an application's child `i` is its item
//! `i`; annotations are not nodes and take no step.

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

/// Two nullary sorts and one with a parameter.
fn sort() -> impl Strategy<Value = Sort> {
    prop_oneof![
        Just(Sort::new("Int")),
        Just(Sort::new("Bool")),
        Just(Sort::with_parameters("List", vec![Sort::new("Int")])),
    ]
}

/// Labels of two names with zero or one sort parameter.
fn label() -> BoxedStrategy<Label> {
    (0_u8..2, prop::collection::vec(sort(), 0..2))
        .prop_map(|(name, parameters)| Label::with_parameters(format!("l{name}"), parameters))
        .boxed()
}

/// Terms over a small alphabet that varies every field `Term::eq` compares besides the
/// children: token texts and sorts, variable names and sorts (or none), label names and
/// label sort parameters.
pub(crate) fn varied_fields() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        (0_u8..2, sort()).prop_map(|(token, sort)| Term::Token {
            token: token.to_string(),
            sort,
        }),
        (0_u8..2, prop::option::of(sort())).prop_map(|(name, sort)| Term::Variable {
            name: format!("X{name}"),
            sort,
        }),
        label().prop_map(Term::InjectedLabel),
        label().prop_map(|label| Term::Apply {
            label,
            arguments: Vec::new()
        }),
    ];
    leaf.prop_recursive(3, 24, 3, |inner| {
        prop_oneof![
            (label(), prop::collection::vec(inner.clone(), 1..3))
                .prop_map(|(label, arguments)| Term::Apply { label, arguments }),
            prop::collection::vec(inner.clone(), 0..3).prop_map(Term::Sequence),
            (inner.clone(), inner.clone()).prop_map(|(left, right)| Term::Rewrite {
                left: Box::new(left),
                right: Box::new(right),
            }),
            (inner.clone(), inner).prop_map(|(pattern, alias)| Term::As {
                pattern: Box::new(pattern),
                alias: Box::new(alias),
            }),
        ]
    })
}

/// A generated sort other than `sort`.
fn other_sort(sort: &Sort) -> Sort {
    if *sort == Sort::new("Int") {
        Sort::new("Bool")
    } else {
        Sort::new("Int")
    }
}

/// A change of one field of a node.
type Edit = Box<dyn Fn(&mut Term)>;

/// Each term that differs from `term` in exactly one field of one node other than its
/// children, with the name of the field: every field `Term::cmp_level` compares besides the
/// children (the variant is changed by the generator's independent draws).
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "the structural nodes have no field besides their children"
)]
pub(crate) fn one_edit_neighbours(term: &Term) -> Vec<(&'static str, Term)> {
    let mut neighbours = Vec::new();
    for (steps, _) in positions(term) {
        let mut edits: Vec<(&'static str, Edit)> = Vec::new();
        match at_path_mut(&mut term.clone(), &steps) {
            Term::Token { .. } => {
                edits.push((
                    "token text",
                    Box::new(|node| {
                        if let Term::Token { token, .. } = node {
                            token.push('\'');
                        }
                    }),
                ));
                edits.push((
                    "token sort",
                    Box::new(|node| {
                        if let Term::Token { sort, .. } = node {
                            *sort = other_sort(sort);
                        }
                    }),
                ));
            }
            Term::Variable { .. } => {
                edits.push((
                    "variable name",
                    Box::new(|node| {
                        if let Term::Variable { name, .. } = node {
                            name.push('\'');
                        }
                    }),
                ));
                edits.push((
                    "variable sort",
                    Box::new(|node| {
                        if let Term::Variable { sort, .. } = node {
                            *sort = match sort {
                                None => Some(Sort::new("Int")),
                                Some(sort) => Some(other_sort(sort)),
                            };
                        }
                    }),
                ));
            }
            Term::InjectedLabel(_) | Term::Apply { .. } => {
                edits.push((
                    "label name",
                    Box::new(|node| {
                        if let Term::InjectedLabel(label) | Term::Apply { label, .. } = node {
                            label.name.push('\'');
                        }
                    }),
                ));
                edits.push((
                    "label parameters",
                    Box::new(|node| {
                        if let Term::InjectedLabel(label) | Term::Apply { label, .. } = node {
                            match label.parameters.first_mut() {
                                Some(parameter) => *parameter = other_sort(parameter),
                                None => label.parameters.push(Sort::new("Int")),
                            }
                        }
                    }),
                ));
            }
            _ => {}
        }
        for (field, edit) in edits {
            let mut neighbour = term.clone();
            edit(at_path_mut(&mut neighbour, &steps));
            neighbours.push((field, neighbour));
        }
    }
    neighbours
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

/// The children of `term`, its annotations removed, by step number (the specification above).
fn children(term: &Term) -> Vec<&Term> {
    match term.unannotated() {
        Term::Rewrite { left, right } => vec![left, right],
        Term::As { pattern, alias } => vec![pattern, alias],
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => items.iter().collect(),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Vec::new(),
        Term::Annotated { .. } => unreachable!("unannotated strips annotations"),
    }
}

/// Every node of `term` (its annotation, when it has one) with the steps that lead to it from
/// `term`.
pub(crate) fn positions(term: &Term) -> Vec<(Vec<u32>, &Term)> {
    let mut found = Vec::new();
    let mut pending = vec![(Vec::new(), term)];
    while let Some((steps, node)) = pending.pop() {
        for (step, child) in (0..).zip(children(node)) {
            let mut child_steps = steps.clone();
            child_steps.push(step);
            pending.push((child_steps, child));
        }
        found.push((steps, node));
    }
    found
}

/// The node `steps` lead to from `term`, its annotation included.
pub(crate) fn at_path_mut<'a>(mut term: &'a mut Term, steps: &[u32]) -> &'a mut Term {
    for step in steps {
        let mut node = term;
        while let Term::Annotated { term: inner, .. } = node {
            node = inner;
        }
        let step = usize::try_from(*step).expect("a step fits usize");
        term = match node {
            Term::Rewrite { left, right } => [&mut **left, &mut **right]
                .into_iter()
                .nth(step)
                .expect("a step names a child"),
            Term::As { pattern, alias } => [&mut **pattern, &mut **alias]
                .into_iter()
                .nth(step)
                .expect("a step names a child"),
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => &mut items[step],
            Term::InjectedLabel(_)
            | Term::Variable { .. }
            | Term::Token { .. }
            | Term::Annotated { .. } => unreachable!("a step names a child"),
        };
    }
    term
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
