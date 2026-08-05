use k_rust::kore::ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind};
use k_rust::kore::normalize;
use k_rust::kore::printer::Printer;
use k_rust::kore::{json, parser};
use proptest::prelude::*;

fn sort() -> impl Strategy<Value = Sort> {
    prop_oneof![
        "[A-Z][A-Za-z0-9]{0,5}".prop_map(Sort::Variable),
        "Sort[A-Z][A-Za-z0-9]{0,5}".prop_map(|name| Sort::Application {
            name,
            arguments: vec![],
        }),
    ]
}

fn symbol() -> impl Strategy<Value = Symbol> {
    (
        "[a-zA-Z][A-Za-z0-9'-]{0,7}",
        prop::collection::vec(sort(), 0..3),
    )
        .prop_map(|(name, sort_parameters)| Symbol {
            name,
            sort_parameters,
        })
}

fn pattern() -> impl Strategy<Value = Pattern> {
    let leaf = prop_oneof![
        any::<String>().prop_map(Pattern::String),
        ("[A-Z][A-Za-z0-9]{0,5}", sort()).prop_map(|(name, sort)| Pattern::Variable(Variable {
            kind: VariableKind::Element,
            name,
            sort,
        })),
        ("@[A-Z][A-Za-z0-9]{0,5}", sort()).prop_map(|(name, sort)| Pattern::Variable(Variable {
            kind: VariableKind::Set,
            name,
            sort,
        })),
        sort().prop_map(|sort| Pattern::Top { sort }),
        sort().prop_map(|sort| Pattern::Bottom { sort }),
        (sort(), any::<String>()).prop_map(|(sort, value)| Pattern::DomainValue { sort, value }),
    ];

    leaf.prop_recursive(5, 128, 8, |inner| {
        prop_oneof![
            (symbol(), prop::collection::vec(inner.clone(), 0..4))
                .prop_map(|(symbol, arguments)| Pattern::Application { symbol, arguments }),
            (sort(), prop::collection::vec(inner.clone(), 0..5))
                .prop_map(|(sort, arguments)| Pattern::And { sort, arguments }),
            (sort(), prop::collection::vec(inner.clone(), 0..5))
                .prop_map(|(sort, arguments)| Pattern::Or { sort, arguments }),
            (
                any::<bool>(),
                symbol(),
                prop::collection::vec(inner.clone(), 1..5)
            )
                .prop_map(|(left, symbol, arguments)| {
                    Pattern::AssociativeApplication {
                        associativity: if left {
                            Associativity::Left
                        } else {
                            Associativity::Right
                        },
                        symbol,
                        arguments,
                    }
                }),
            (sort(), inner.clone()).prop_map(|(sort, argument)| Pattern::Not {
                sort,
                argument: Box::new(argument),
            }),
            (sort(), inner.clone()).prop_map(|(sort, argument)| Pattern::Next {
                sort,
                argument: Box::new(argument),
            }),
            (sort(), inner.clone(), inner.clone()).prop_map(|(sort, left, right)| {
                Pattern::Implies {
                    sort,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }),
            (sort(), inner.clone(), inner.clone()).prop_map(|(sort, left, right)| Pattern::Iff {
                sort,
                left: Box::new(left),
                right: Box::new(right),
            }),
            (sort(), inner.clone(), inner.clone()).prop_map(|(sort, left, right)| {
                Pattern::Rewrites {
                    sort,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }),
            (sort(), "[A-Z][A-Za-z0-9]{0,5}", sort(), inner.clone()).prop_map(
                |(sort, name, variable_sort, body)| Pattern::Exists {
                    sort,
                    variable: Variable {
                        kind: VariableKind::Element,
                        name,
                        sort: variable_sort
                    },
                    body: Box::new(body),
                }
            ),
            (sort(), "[A-Z][A-Za-z0-9]{0,5}", sort(), inner.clone()).prop_map(
                |(sort, name, variable_sort, body)| Pattern::Forall {
                    sort,
                    variable: Variable {
                        kind: VariableKind::Element,
                        name,
                        sort: variable_sort
                    },
                    body: Box::new(body),
                }
            ),
            ("@[A-Z][A-Za-z0-9]{0,5}", sort(), inner.clone()).prop_map(|(name, sort, body)| {
                Pattern::Mu {
                    variable: Variable {
                        kind: VariableKind::Set,
                        name,
                        sort,
                    },
                    body: Box::new(body),
                }
            }),
            ("@[A-Z][A-Za-z0-9]{0,5}", sort(), inner.clone()).prop_map(|(name, sort, body)| {
                Pattern::Nu {
                    variable: Variable {
                        kind: VariableKind::Set,
                        name,
                        sort,
                    },
                    body: Box::new(body),
                }
            }),
            (sort(), sort(), inner.clone()).prop_map(|(operand_sort, result_sort, argument)| {
                Pattern::Ceil {
                    operand_sort,
                    result_sort,
                    argument: Box::new(argument),
                }
            }),
            (sort(), sort(), inner.clone()).prop_map(|(operand_sort, result_sort, argument)| {
                Pattern::Floor {
                    operand_sort,
                    result_sort,
                    argument: Box::new(argument),
                }
            }),
            (sort(), sort(), inner.clone(), inner.clone()).prop_map(
                |(operand_sort, result_sort, left, right)| Pattern::Equals {
                    operand_sort,
                    result_sort,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            ),
            (sort(), sort(), inner.clone(), inner.clone()).prop_map(
                |(operand_sort, result_sort, left, right)| Pattern::In {
                    operand_sort,
                    result_sort,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            ),
        ]
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn compact_text_round_trip(pattern in pattern()) {
        let text = Printer::compact().print_pattern(&pattern);
        let parsed = parser::parse_pattern(&text).unwrap();
        prop_assert_eq!(parsed, pattern);
    }

    #[test]
    fn pretty_text_round_trip(pattern in pattern(), width in 20usize..120) {
        let text = Printer::pretty(width).print_pattern(&pattern);
        let parsed = parser::parse_pattern(&text).unwrap();
        prop_assert_eq!(parsed, pattern);
    }

    #[test]
    fn json_round_trip(pattern in pattern()) {
        let encoded = json::to_string(&pattern).unwrap();
        let decoded = json::from_str(&encoded).unwrap();
        prop_assert_eq!(decoded, pattern);
    }

    #[test]
    fn kast_normalization_is_idempotent(pattern in pattern()) {
        let normalized = normalize::for_kast(&pattern);
        prop_assert_eq!(normalize::for_kast(&normalized), normalized);
    }
}
