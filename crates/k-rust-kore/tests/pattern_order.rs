//! Laws of the `Pattern` order.
//!
//! `Ord for Pattern` is hand-written with an explicit work list so that deep patterns do not
//! overflow the stack, and it must give the order `#[derive(Ord)]` would: variant rank in
//! declaration order, the variant's scalar fields in declaration order under their own `Ord`
//! (strings byte-wise), then children left to right, then child count.
//! `Derived` below is that derive spelled out on a mirror of the enum; the properties check
//! `Pattern::cmp` against it and check the order laws and structural equality directly.

use std::cmp::Ordering;

use k_rust_kore::kore::ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind};
use k_rust_kore::kore::parser::parse_pattern;
use proptest::prelude::*;

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Derived {
    String(String),
    Variable(Variable),
    Application {
        symbol: Symbol,
        arguments: Vec<Derived>,
    },
    Top {
        sort: Sort,
    },
    Bottom {
        sort: Sort,
    },
    And {
        sort: Sort,
        arguments: Vec<Derived>,
    },
    Or {
        sort: Sort,
        arguments: Vec<Derived>,
    },
    Not {
        sort: Sort,
        argument: Box<Derived>,
    },
    Next {
        sort: Sort,
        argument: Box<Derived>,
    },
    Implies {
        sort: Sort,
        left: Box<Derived>,
        right: Box<Derived>,
    },
    Iff {
        sort: Sort,
        left: Box<Derived>,
        right: Box<Derived>,
    },
    Rewrites {
        sort: Sort,
        left: Box<Derived>,
        right: Box<Derived>,
    },
    Exists {
        sort: Sort,
        variable: Variable,
        body: Box<Derived>,
    },
    Forall {
        sort: Sort,
        variable: Variable,
        body: Box<Derived>,
    },
    Mu {
        variable: Variable,
        body: Box<Derived>,
    },
    Nu {
        variable: Variable,
        body: Box<Derived>,
    },
    Ceil {
        operand_sort: Sort,
        result_sort: Sort,
        argument: Box<Derived>,
    },
    Floor {
        operand_sort: Sort,
        result_sort: Sort,
        argument: Box<Derived>,
    },
    Equals {
        operand_sort: Sort,
        result_sort: Sort,
        left: Box<Derived>,
        right: Box<Derived>,
    },
    In {
        operand_sort: Sort,
        result_sort: Sort,
        left: Box<Derived>,
        right: Box<Derived>,
    },
    DomainValue {
        sort: Sort,
        value: String,
    },
    AssociativeApplication {
        associativity: Associativity,
        symbol: Symbol,
        arguments: Vec<Derived>,
    },
}

impl From<&Pattern> for Derived {
    fn from(pattern: &Pattern) -> Self {
        let boxed = |child: &Pattern| Box::new(Derived::from(child));
        let list = |children: &[Pattern]| children.iter().map(Derived::from).collect();
        match pattern {
            Pattern::String(value) => Derived::String(value.clone()),
            Pattern::Variable(variable) => Derived::Variable(variable.clone()),
            Pattern::Application { symbol, arguments } => Derived::Application {
                symbol: symbol.clone(),
                arguments: list(arguments),
            },
            Pattern::Top { sort } => Derived::Top { sort: sort.clone() },
            Pattern::Bottom { sort } => Derived::Bottom { sort: sort.clone() },
            Pattern::And { sort, arguments } => Derived::And {
                sort: sort.clone(),
                arguments: list(arguments),
            },
            Pattern::Or { sort, arguments } => Derived::Or {
                sort: sort.clone(),
                arguments: list(arguments),
            },
            Pattern::Not { sort, argument } => Derived::Not {
                sort: sort.clone(),
                argument: boxed(argument),
            },
            Pattern::Next { sort, argument } => Derived::Next {
                sort: sort.clone(),
                argument: boxed(argument),
            },
            Pattern::Implies { sort, left, right } => Derived::Implies {
                sort: sort.clone(),
                left: boxed(left),
                right: boxed(right),
            },
            Pattern::Iff { sort, left, right } => Derived::Iff {
                sort: sort.clone(),
                left: boxed(left),
                right: boxed(right),
            },
            Pattern::Rewrites { sort, left, right } => Derived::Rewrites {
                sort: sort.clone(),
                left: boxed(left),
                right: boxed(right),
            },
            Pattern::Exists {
                sort,
                variable,
                body,
            } => Derived::Exists {
                sort: sort.clone(),
                variable: variable.clone(),
                body: boxed(body),
            },
            Pattern::Forall {
                sort,
                variable,
                body,
            } => Derived::Forall {
                sort: sort.clone(),
                variable: variable.clone(),
                body: boxed(body),
            },
            Pattern::Mu { variable, body } => Derived::Mu {
                variable: variable.clone(),
                body: boxed(body),
            },
            Pattern::Nu { variable, body } => Derived::Nu {
                variable: variable.clone(),
                body: boxed(body),
            },
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => Derived::Ceil {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                argument: boxed(argument),
            },
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => Derived::Floor {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                argument: boxed(argument),
            },
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => Derived::Equals {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                left: boxed(left),
                right: boxed(right),
            },
            Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => Derived::In {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                left: boxed(left),
                right: boxed(right),
            },
            Pattern::DomainValue { sort, value } => Derived::DomainValue {
                sort: sort.clone(),
                value: value.clone(),
            },
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => Derived::AssociativeApplication {
                associativity: *associativity,
                symbol: symbol.clone(),
                arguments: list(arguments),
            },
        }
    }
}

// Names start with an upper-case letter so they never collide with a KORE keyword; a small
// alphabet makes equal names, and therefore comparisons that reach the children, common.
fn name() -> impl Strategy<Value = String> {
    "[A-C][a-c0-9']{0,2}"
}

fn sort() -> impl Strategy<Value = Sort> {
    let leaf = prop_oneof![
        name().prop_map(Sort::Variable),
        name().prop_map(|name| Sort::Application {
            name,
            arguments: Vec::new(),
        }),
    ];
    leaf.prop_recursive(2, 6, 2, |inner| {
        (name(), prop::collection::vec(inner, 1..3))
            .prop_map(|(name, arguments)| Sort::Application { name, arguments })
    })
}

fn symbol() -> impl Strategy<Value = Symbol> {
    (name(), prop::collection::vec(sort(), 0..3)).prop_map(|(name, sort_parameters)| Symbol {
        name,
        sort_parameters,
    })
}

// A set variable's name carries its `@` prefix, as the parser stores it.
fn variable(kind: VariableKind) -> impl Strategy<Value = Variable> {
    let prefix = match kind {
        VariableKind::Element => "",
        VariableKind::Set => "@",
    };
    (name(), sort()).prop_map(move |(name, sort)| Variable {
        kind,
        name: format!("{prefix}{name}"),
        sort,
    })
}

fn any_variable() -> impl Strategy<Value = Variable> {
    prop_oneof![variable(VariableKind::Element), variable(VariableKind::Set)]
}

// Digit runs of different lengths and code points outside the BMP are the inputs on which a
// byte-wise order differs from the alphanumeric and UTF-16 orders this crate used to mirror.
fn text() -> impl Strategy<Value = String> {
    prop_oneof![
        3 => "[a-b0-9]{0,4}",
        1 => prop::collection::vec(any::<char>(), 0..3).prop_map(String::from_iter),
    ]
}

fn pattern() -> impl Strategy<Value = Pattern> {
    let leaf = prop_oneof![
        text().prop_map(Pattern::String),
        any_variable().prop_map(Pattern::Variable),
        sort().prop_map(|sort| Pattern::Top { sort }),
        sort().prop_map(|sort| Pattern::Bottom { sort }),
        (sort(), text()).prop_map(|(sort, value)| Pattern::DomainValue { sort, value }),
    ];
    leaf.prop_recursive(4, 24, 3, |inner| {
        let boxed = || inner.clone().prop_map(Box::new);
        let list = |range| prop::collection::vec(inner.clone(), range);
        prop_oneof![
            (symbol(), list(0..3))
                .prop_map(|(symbol, arguments)| Pattern::Application { symbol, arguments }),
            (sort(), list(0..3)).prop_map(|(sort, arguments)| Pattern::And { sort, arguments }),
            (sort(), list(0..3)).prop_map(|(sort, arguments)| Pattern::Or { sort, arguments }),
            (sort(), boxed()).prop_map(|(sort, argument)| Pattern::Not { sort, argument }),
            (sort(), boxed()).prop_map(|(sort, argument)| Pattern::Next { sort, argument }),
            (sort(), boxed(), boxed()).prop_map(|(sort, left, right)| Pattern::Implies {
                sort,
                left,
                right
            }),
            (sort(), boxed(), boxed()).prop_map(|(sort, left, right)| Pattern::Iff {
                sort,
                left,
                right
            }),
            (sort(), boxed(), boxed()).prop_map(|(sort, left, right)| Pattern::Rewrites {
                sort,
                left,
                right
            }),
            (sort(), variable(VariableKind::Element), boxed()).prop_map(
                |(sort, variable, body)| Pattern::Exists {
                    sort,
                    variable,
                    body
                }
            ),
            (sort(), variable(VariableKind::Element), boxed()).prop_map(
                |(sort, variable, body)| Pattern::Forall {
                    sort,
                    variable,
                    body
                }
            ),
            (variable(VariableKind::Set), boxed())
                .prop_map(|(variable, body)| Pattern::Mu { variable, body }),
            (variable(VariableKind::Set), boxed())
                .prop_map(|(variable, body)| Pattern::Nu { variable, body }),
            (sort(), sort(), boxed()).prop_map(|(operand_sort, result_sort, argument)| {
                Pattern::Ceil {
                    operand_sort,
                    result_sort,
                    argument,
                }
            }),
            (sort(), sort(), boxed()).prop_map(|(operand_sort, result_sort, argument)| {
                Pattern::Floor {
                    operand_sort,
                    result_sort,
                    argument,
                }
            }),
            (sort(), sort(), boxed(), boxed()).prop_map(
                |(operand_sort, result_sort, left, right)| Pattern::Equals {
                    operand_sort,
                    result_sort,
                    left,
                    right,
                }
            ),
            (sort(), sort(), boxed(), boxed()).prop_map(
                |(operand_sort, result_sort, left, right)| Pattern::In {
                    operand_sort,
                    result_sort,
                    left,
                    right,
                }
            ),
            (
                prop_oneof![Just(Associativity::Left), Just(Associativity::Right)],
                symbol(),
                list(1..3)
            )
                .prop_map(|(associativity, symbol, arguments)| {
                    Pattern::AssociativeApplication {
                        associativity,
                        symbol,
                        arguments,
                    }
                }),
        ]
    })
}

proptest! {
    #[test]
    fn cmp_is_the_derived_order(a in pattern(), b in pattern()) {
        prop_assert_eq!(a.cmp(&b), Derived::from(&a).cmp(&Derived::from(&b)));
    }

    #[test]
    fn cmp_is_antisymmetric(a in pattern(), b in pattern()) {
        prop_assert_eq!(a.cmp(&a), Ordering::Equal);
        prop_assert_eq!(a.cmp(&b), b.cmp(&a).reverse());
    }

    #[test]
    fn cmp_is_transitive(a in pattern(), b in pattern(), c in pattern()) {
        let patterns = [&a, &b, &c];
        for x in patterns {
            for y in patterns {
                for z in patterns {
                    if x <= y && y <= z {
                        prop_assert!(x <= z, "{x} <= {y} <= {z} but {x} > {z}");
                    }
                }
            }
        }
    }

    #[test]
    fn eq_agrees_with_printed_text(a in pattern(), b in pattern()) {
        let text = a.to_string();
        let reparsed = parse_pattern(&text).expect("printed KORE should parse");
        let cloned = a.clone();
        prop_assert_eq!(a == b, text == b.to_string());
        prop_assert_eq!(a == reparsed, text == reparsed.to_string());
        prop_assert!(a == reparsed);
        prop_assert!(a == cloned);
    }
}
