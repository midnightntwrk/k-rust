use std::cmp::Ordering;

use k_rust::definition::{
    Associativity, Attributes, ProductionItem, Sentence, compare_sentences, compare_terms,
    sentence_equivalent,
};
use k_rust::kast::{Label, Sort, Term};
use proptest::prelude::*;

fn sort() -> impl Strategy<Value = Sort> {
    "[#A-Z][A-Za-z0-9]{0,5}"
        .prop_map(Sort::new)
        .prop_recursive(2, 12, 2, |inner| {
            ("[#A-Z][A-Za-z0-9]{0,5}", prop::collection::vec(inner, 1..3))
                .prop_map(|(name, parameters)| Sort { name, parameters })
        })
}

fn label() -> impl Strategy<Value = Label> {
    (
        "[A-Za-z_#][A-Za-z0-9_]{0,7}",
        prop::collection::vec(sort(), 0..3),
    )
        .prop_map(|(name, parameters)| Label { name, parameters })
}

fn term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        (any::<String>(), sort()).prop_map(|(token, sort)| Term::Token { token, sort }),
        ("[A-Z_][A-Za-z0-9_]{0,6}", prop::option::of(sort()))
            .prop_map(|(name, sort)| Term::Variable { name, sort }),
        label().prop_map(Term::InjectedLabel),
    ];
    leaf.prop_recursive(3, 40, 5, |inner| {
        prop_oneof![
            (label(), prop::collection::vec(inner.clone(), 0..3))
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

fn sentence() -> impl Strategy<Value = Sentence> {
    (0_u8..11, "[A-Z][A-Za-z0-9]{0,5}", any::<u8>()).prop_map(|(kind, name, value)| {
        let attributes = Attributes::default();
        let variable = || Term::variable(name.clone());
        match kind {
            0 => Sentence::SyntaxSort {
                parameters: vec![Sort::new(format!("P{value}"))],
                sort: Sort::new(name),
                attributes,
            },
            1 => Sentence::SortSynonym {
                new_sort: Sort::new(name),
                old_sort: Sort::new(format!("S{value}")),
                attributes,
            },
            2 => Sentence::SyntaxLexical {
                name,
                regex: format!("[a-z]{{{value}}}"),
                attributes,
            },
            3 => Sentence::Production {
                label: Some(Label::new(name)),
                parameters: Vec::new(),
                sort: Sort::new(format!("S{value}")),
                items: vec![ProductionItem::Terminal(value.to_string())],
                attributes,
            },
            4 => Sentence::SyntaxAssociativity {
                associativity: match value % 4 {
                    0 => Associativity::Left,
                    1 => Associativity::Right,
                    2 => Associativity::NonAssoc,
                    _ => Associativity::Unspecified,
                },
                tags: vec![name, format!("T{value}")],
                attributes,
            },
            5 => Sentence::SyntaxPriority {
                priorities: vec![vec![name, format!("T{value}")]],
                attributes,
            },
            6 => Sentence::ContextAlias {
                body: variable(),
                requires: Term::variable(format!("R{value}")),
                attributes,
            },
            7 => Sentence::Context {
                body: variable(),
                requires: Term::variable(format!("R{value}")),
                attributes,
            },
            8 => Sentence::Rule {
                body: variable(),
                requires: Term::variable(format!("R{value}")),
                ensures: Term::variable(format!("E{value}")),
                attributes,
            },
            9 => Sentence::Claim {
                body: variable(),
                requires: Term::variable(format!("R{value}")),
                ensures: Term::variable(format!("E{value}")),
                attributes,
            },
            _ => Sentence::Bubble {
                sentence_type: name,
                contents: value.to_string(),
                attributes,
            },
        }
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn scala_comparison_is_antisymmetric(left in sentence(), right in sentence()) {
        let left_right = compare_sentences(&left, &right).unwrap();
        let right_left = compare_sentences(&right, &left).unwrap();
        prop_assert_eq!(left_right, right_left.reverse());
    }

    #[test]
    fn scala_comparison_is_transitive(left in sentence(), middle in sentence(), right in sentence()) {
        let left_middle = compare_sentences(&left, &middle).unwrap();
        let middle_right = compare_sentences(&middle, &right).unwrap();
        if left_middle != Ordering::Greater && middle_right != Ordering::Greater {
            prop_assert_ne!(compare_sentences(&left, &right).unwrap(), Ordering::Greater);
        }
    }

    #[test]
    fn scala_equivalence_is_reflexive_and_symmetric(left in sentence(), right in sentence()) {
        prop_assert!(sentence_equivalent(&left, &left));
        prop_assert_eq!(
            sentence_equivalent(&left, &right),
            sentence_equivalent(&right, &left),
        );
    }

    #[test]
    fn scala_term_comparison_obeys_ordering_laws(left in term(), middle in term(), right in term()) {
        prop_assert_eq!(compare_terms(&left, &left), Ordering::Equal);
        prop_assert_eq!(compare_terms(&left, &right), compare_terms(&right, &left).reverse());
        if compare_terms(&left, &middle) != Ordering::Greater
            && compare_terms(&middle, &right) != Ordering::Greater
        {
            prop_assert_ne!(compare_terms(&left, &right), Ordering::Greater);
        }
    }
}
