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
        self, ConjunctionShape, External, Printable, ResultSort, conjunction, connective_source,
        constrained_pattern, disjunction, ml_pattern, predicate_pattern, sort,
    },
    rewrite::Pattern,
    rule::{Absence, KeyedCollection, Predicate},
    term::{CollectionSymbols, ListDefinition, MapDefinition, Sort, Term, Variable},
    transition::PatternDigest,
};

/// Predicates over generated terms, with Boolean domain values on either side of equalities so
/// that the orientation rule is exercised, and every connective and binder.
fn predicate() -> impl Strategy<Value = Predicate> {
    let boolean = prop_oneof![Just("true"), Just("false")]
        .prop_map(|value| Term::raw_domain_value(Sort::builtin(BuiltinSort::Bool), value));
    let operand = prop_oneof![3 => generators::term(), 1 => boolean];
    let leaf =
        prop_oneof![
            Just(Predicate::True),
            Just(Predicate::False),
            operand.clone().prop_map(Predicate::Term),
            (operand.clone(), operand.clone())
                .prop_map(|(left, right)| Predicate::Equals(left, right)),
            operand.clone().prop_map(Predicate::Ceil),
            operand.clone().prop_map(Predicate::Floor),
            (operand.clone(), operand.clone()).prop_map(|(left, right)| Predicate::In(left, right)),
            (operand.clone(), operand, any::<bool>())
                .prop_map(|(key, rest, map)| Absence::predicate(keyed(map), key, rest)),
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

/// A map or a set collection for absences over generated terms.
fn keyed(map: bool) -> KeyedCollection {
    let symbols = |prefix: &str| CollectionSymbols {
        unit: format!("{prefix}Unit").into(),
        element: format!("{prefix}Item").into(),
        concat: format!("{prefix}Concat").into(),
    };
    if map {
        KeyedCollection::Map(std::sync::Arc::new(MapDefinition {
            symbols: symbols("map"),
            key_sort: Sort::simple("SortKItem"),
            value_sort: Sort::simple("SortKItem"),
            map_sort: "SortMap".into(),
        }))
    } else {
        KeyedCollection::Set(std::sync::Arc::new(ListDefinition {
            symbols: symbols("set"),
            element_sort: Sort::simple("SortKItem"),
            list_sort: "SortSet".into(),
        }))
    }
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
        let printable = Printable::predicate(&predicate);
        let source = External::Predicate {
            predicate: printable.source(),
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
        let printable = Printable::pattern(&pattern);
        prop_assert_eq!(&materialize(External::Constrained(printable.source())), &expected);
        assert_same_text(External::Constrained(printable.source()), &expected);
        let expected_digest: [u8; 32] = Sha256::digest(expected.to_string().as_bytes()).into();
        prop_assert_eq!(PatternDigest::of(&pattern).into_bytes(), expected_digest);
    }

    /// A binding source is the equality of the variable and the value.
    #[test]
    fn binding_sources_match_the_equality(
        value in prop_oneof![
            generators::term(),
            prop_oneof![Just("true"), Just("false")]
                .prop_map(|value| Term::raw_domain_value(Sort::builtin(BuiltinSort::Bool), value)),
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

    /// An equation source is the equality of the variable and the value at the variable's sort,
    /// in the order given, whatever the value is.
    #[test]
    fn equation_sources_match_the_equality_in_their_order(
        value in prop_oneof![
            generators::term(),
            prop_oneof![Just("true"), Just("false")]
                .prop_map(|value| Term::raw_domain_value(Sort::builtin(BuiltinSort::Bool), value)),
        ],
        value_first in any::<bool>(),
    ) {
        let result_sort = Sort::simple("SortGeneratedTopCell");
        let variable = Variable::new("Var'Unds'Gen0", Sort::builtin(BuiltinSort::Bool));
        let (left, right) = (externalize::term(&Term::variable(variable.clone())), externalize::term(&value));
        let (left, right) = if value_first { (right, left) } else { (left, right) };
        let expected = kore::Pattern::Equals {
            operand_sort: Box::new(sort(&variable.sort)),
            result_sort: sort(&result_sort),
            left: Box::new(left),
            right: Box::new(right),
        };
        let source = External::Equation {
            variable: &variable,
            value: &value,
            value_first,
            sort: &result_sort,
        };
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

fn element(name: &str) -> Variable {
    Variable::new(name, Sort::simple("SortK"))
}

/// `\exists binder. binder = free`, the body of which mentions `free` free.
fn bound_next_to(binder: &str, free: &str) -> Predicate {
    Predicate::Exists(
        element(binder),
        Box::new(Predicate::Equals(
            Term::variable(element(binder)),
            Term::variable(element(free)),
        )),
    )
}

/// The printed binder and the printed variables of the body of `\exists` in `pattern`.
fn printed_binder(pattern: &kore::Pattern) -> (String, Vec<String>) {
    let kore::Pattern::Exists { variable, body, .. } = pattern else {
        panic!("expected an existential: {pattern}");
    };
    let kore::Pattern::Equals { left, right, .. } = body.as_ref() else {
        panic!("expected an equality: {pattern}");
    };
    let name = |side: &kore::Pattern| match side {
        kore::Pattern::Variable(variable) => variable.name.clone(),
        other => panic!("expected a variable: {other}"),
    };
    (variable.name.clone(), vec![name(left), name(right)])
}

/// A binder whose printed spelling is the spelling of another variable free in its body is
/// renamed by the printer, so the printed pattern binds what the internal one binds: a mint
/// `Ex#X!0` bound next to a query variable spelled `Ex-hX-b0`, and a query binder spelled
/// `Ex-hX-b0` next to the free mint.
#[test]
fn a_binder_spelled_like_a_free_variable_of_its_body_is_renamed() {
    let result_sort = Sort::simple("SortK");
    for (binder, free) in [("Ex#X!0", "Ex-hX-b0"), ("Ex-hX-b0", "Ex#X!0")] {
        let predicate = bound_next_to(binder, free);
        let printed = predicate_pattern(&predicate, &result_sort);
        let (binder_spelling, body) = printed_binder(&printed);
        assert_ne!(binder_spelling, "Ex-hX-b0", "{printed}");
        assert_eq!(body, vec![binder_spelling.clone(), "Ex-hX-b0".to_owned()]);
        // The streaming source agrees with the builder.
        let printable = Printable::predicate(&predicate);
        let source = External::Predicate {
            predicate: printable.source(),
            sort: ResultSort::Given(&result_sort),
            preserve_terms: false,
        };
        assert_eq!(materialize(source), printed);
        assert_same_text(source, &printed);
        let pattern = Pattern {
            term: Term::variable(element(free)),
            constraints: vec![predicate],
        };
        let printable = Printable::pattern(&pattern);
        assert_eq!(
            materialize(External::Constrained(printable.source())),
            constrained_pattern(&pattern)
        );
    }
}

/// Whether a predicate needs a rename is decided over all of it: a binder captures a variable
/// spelled like it that occurs free several connectives and binders below, and two variables
/// spelled alike under sibling binders, neither in the scope of the other, rename nothing.
#[test]
fn a_spelling_clash_is_renamed_only_where_a_binder_captures() {
    let result_sort = Sort::simple("SortK");
    let deep = Predicate::Exists(
        element("Ex#X!0"),
        Box::new(Predicate::And(vec![
            Predicate::True,
            Predicate::Forall(
                element("Y"),
                Box::new(Predicate::Not(Box::new(bound_next_to("Z", "Ex-hX-b0")))),
            ),
        ])),
    );
    let printed = predicate_pattern(&deep, &result_sort);
    let kore::Pattern::Exists { variable, .. } = &printed else {
        panic!("expected an existential: {printed}");
    };
    assert_ne!(variable.name, "Ex-hX-b0", "{printed}");
    assert!(externalize::apart_binders(&deep).is_some());
    let siblings = Predicate::And(vec![
        bound_next_to("Ex#X!0", "Y"),
        bound_next_to("Ex-hX-b0", "Y"),
    ]);
    assert_eq!(externalize::apart_binders(&siblings), None);
}

/// A binder that captures nothing keeps its name, even when it is spelled like a variable free
/// outside its body or is the free variable itself.
#[test]
fn a_binder_that_captures_nothing_keeps_its_name() {
    let result_sort = Sort::simple("SortK");
    let predicate = bound_next_to("Ex#X!0", "Y");
    let (binder, _) = printed_binder(&predicate_pattern(&predicate, &result_sort));
    assert_eq!(binder, "Ex-hX-b0");
    let pattern = Pattern {
        term: Term::variable(element("Ex-hX-b0")),
        constraints: vec![predicate],
    };
    let printable = Printable::pattern(&pattern);
    assert!(std::ptr::eq(&*printable.source(), &pattern));
}
