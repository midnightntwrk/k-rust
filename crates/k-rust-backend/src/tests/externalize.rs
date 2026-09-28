//! Externalization through [`External`] sources against the recursive tree builders of
//! `externalize`: a source must materialize to the tree the builder returns, print the same
//! bytes at every width, and compare in the order of the trees.

use k_rust_kore::kore::{
    ast as kore,
    node::{PatternSource, compare, flatten_at, materialize},
    printer::Printer,
};
use k_rust_kore::names::BuiltinSort;
use proptest::prelude::*;
use sha2::{Digest, Sha256};

use super::lean_bridge::generators;
use crate::{
    externalize::{
        self, ConjunctionShape, External, ResultSort, conjunction, connective_source,
        constrained_pattern, disjunction, ml_pattern, predicate_pattern, sort,
    },
    rewrite::Pattern,
    rule::Predicate,
    term::{Sort, Term, Variable},
    transition::PatternDigest,
};

/// Predicates over generated terms, with Boolean domain values on either side of equalities so
/// that the orientation rule is exercised, and every connective and binder.
fn predicate() -> impl Strategy<Value = Predicate> {
    let boolean = prop_oneof![Just("true"), Just("false")]
        .prop_map(|value| Term::domain_value(Sort::builtin(BuiltinSort::Bool), value));
    let operand = prop_oneof![3 => generators::term(), 1 => boolean];
    let leaf = prop_oneof![
        Just(Predicate::True),
        Just(Predicate::False),
        operand.clone().prop_map(Predicate::Term),
        (operand.clone(), operand.clone()).prop_map(|(left, right)| Predicate::Equals(left, right)),
        operand.clone().prop_map(Predicate::Ceil),
        operand.clone().prop_map(Predicate::Floor),
        (operand.clone(), operand).prop_map(|(left, right)| Predicate::In(left, right)),
    ];
    leaf.prop_recursive(3, 24, 3, |inner| {
        let variable = prop_oneof![Just("X"), Just("Z")]
            .prop_map(|name| Variable::new(name, Sort::simple("SortKItem")));
        prop_oneof![
            inner
                .clone()
                .prop_map(|inner| Predicate::Not(Box::new(inner))),
            prop::collection::vec(inner.clone(), 0..3).prop_map(Predicate::And),
            prop::collection::vec(inner.clone(), 0..3).prop_map(Predicate::Or),
            (inner.clone(), inner.clone())
                .prop_map(|(left, right)| Predicate::Implies(Box::new(left), Box::new(right))),
            (inner.clone(), inner.clone())
                .prop_map(|(left, right)| Predicate::Iff(Box::new(left), Box::new(right))),
            (variable.clone(), inner.clone())
                .prop_map(|(variable, inner)| Predicate::Exists(variable, Box::new(inner))),
            (variable, inner)
                .prop_map(|(variable, inner)| Predicate::Forall(variable, Box::new(inner))),
        ]
    })
}

/// The text of `source` and of `pattern` at a narrow, a medium, and an unbounded width.
fn assert_same_text<'a, S: PatternSource<'a>>(source: S, pattern: &kore::Pattern) {
    for printer in [
        Printer::pretty(24),
        Printer::pretty(100),
        Printer::compact(),
    ] {
        let mut printed = Vec::new();
        printer.write_source(source.clone(), &mut printed).unwrap();
        assert_eq!(
            String::from_utf8(printed).unwrap(),
            printer.print_pattern(pattern)
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// A term source materializes to the tree the recursive builder returns and prints the
    /// same text.
    #[test]
    fn term_sources_match_the_tree_builder(term in generators::term()) {
        let expected = externalize::term(&term);
        prop_assert_eq!(&materialize(External::Term(&term)), &expected);
        assert_same_text(External::Term(&term), &expected);
    }

    /// Comparing two term sources gives the order of their materialized trees, and a term
    /// source compares equal to itself without being read.
    #[test]
    fn term_sources_compare_as_their_trees(
        left in generators::term_with_ground_keys(),
        right in generators::term_with_ground_keys(),
    ) {
        let expected = externalize::term(&left).cmp(&externalize::term(&right));
        prop_assert_eq!(compare(External::Term(&left), External::Term(&right)), expected);
        prop_assert_eq!(
            compare(External::Term(&left), External::Term(&left)),
            std::cmp::Ordering::Equal
        );
        let (left, right) = (externalize::term(&left), externalize::term(&right));
        prop_assert_eq!(compare(&left, &right), expected);
    }

    /// Predicate sources, with and without bare terms preserved, match the recursive builder.
    #[test]
    fn predicate_sources_match_the_tree_builder(
        predicate in predicate(),
        preserve_terms in any::<bool>(),
    ) {
        let result_sort = Sort::simple("SortGeneratedTopCell");
        let source = External::Predicate {
            predicate: &predicate,
            sort: ResultSort::Given(&result_sort),
            preserve_terms,
        };
        let expected = if preserve_terms {
            ml_pattern(&predicate, &result_sort)
        } else {
            predicate_pattern(&predicate, &result_sort)
        };
        prop_assert_eq!(&materialize(source), &expected);
        assert_same_text(source, &expected);
    }

    /// Constrained-pattern sources match the recursive builder, including the `\bottom` of a
    /// false constraint set and the grouping of two or more constraints.
    #[test]
    fn constrained_sources_match_the_tree_builder(
        term in generators::term(),
        constraints in prop::collection::vec(predicate(), 0..4),
    ) {
        let pattern = Pattern { term, constraints };
        let expected = constrained_pattern(&pattern);
        prop_assert_eq!(&materialize(External::Constrained(&pattern)), &expected);
        assert_same_text(External::Constrained(&pattern), &expected);
        let expected_digest: [u8; 32] = Sha256::digest(expected.to_string().as_bytes()).into();
        prop_assert_eq!(PatternDigest::of(&pattern).into_bytes(), expected_digest);
    }

    /// A binding source is the equality of the variable and the value.
    #[test]
    fn binding_sources_match_the_equality(
        value in prop_oneof![
            generators::term(),
            prop_oneof![Just("true"), Just("false")]
                .prop_map(|value| Term::domain_value(Sort::builtin(BuiltinSort::Bool), value)),
        ],
        set in any::<bool>(),
    ) {
        let result_sort = Sort::simple("SortGeneratedTopCell");
        let variable = if set {
            Variable::set("V", Sort::simple("SortKItem"))
        } else {
            Variable::new("Var'Unds'Gen0", Sort::builtin(BuiltinSort::Bool))
        };
        let expected = predicate_pattern(
            &Predicate::Equals(Term::variable(variable.clone()), value.clone()),
            &result_sort,
        );
        let source = External::Binding { variable: &variable, value: &value, sort: &result_sort };
        prop_assert_eq!(&materialize(source), &expected);
    }

    /// A connective source of term operands is the `conjunction`/`disjunction` of their trees in
    /// every shape, and flattening it at its sort returns the operands.
    #[test]
    fn connective_sources_match_the_builders(
        terms in prop::collection::vec(generators::term(), 0..9),
        and in any::<bool>(),
        shape in prop_oneof![
            Just(ConjunctionShape::Flat),
            Just(ConjunctionShape::LeftNested),
            Just(ConjunctionShape::Balanced),
        ],
    ) {
        let result_sort = sort(&Sort::simple("SortGeneratedTopCell"));
        let operands = terms.iter().map(External::Term).collect::<Vec<_>>();
        let trees = terms.iter().map(externalize::term).collect::<Vec<_>>();
        let expected = if and {
            conjunction(&result_sort, trees.clone(), shape)
        } else {
            disjunction(&result_sort, trees.clone(), shape)
        };
        let source = connective_source(&result_sort, &operands, shape, and);
        prop_assert_eq!(source.map(materialize), expected.clone());
        if let (Some(source), Some(expected)) = (source, expected) {
            let flattened = flatten_at(source, &result_sort, and)
                .into_iter()
                .map(materialize)
                .collect::<Vec<_>>();
            let reference = if and {
                expected.into_conjuncts_at(&result_sort)
            } else {
                expected.into_disjuncts_at(&result_sort)
            };
            prop_assert_eq!(flattened, reference);
        }
    }
}
