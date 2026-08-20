//! Explicit semantic normalization for consumers such as KORE-to-KAST conversion.

use super::ast::{Associativity, Pattern};

/// Converts syntax-preserving KORE into the shape expected at the KAST boundary.
///
/// Empty and unary conjunctions/disjunctions follow scala-kore's builders, and
/// associative wrappers become binary application trees. Unlike pyk's current
/// `RightAssoc.pattern`, symbol sort parameters are preserved in both directions.
pub fn for_kast(pattern: &Pattern) -> Pattern {
    use Pattern::*;

    let child = |pattern: &Pattern| Box::new(for_kast(pattern));
    match pattern {
        String(value) => String(value.clone()),
        Variable(variable) => Variable(variable.clone()),
        Application { symbol, arguments } => Application {
            symbol: symbol.clone(),
            arguments: arguments.iter().map(for_kast).collect(),
        },
        Top { sort } => Top { sort: sort.clone() },
        Bottom { sort } => Bottom { sort: sort.clone() },
        And { sort, arguments } => {
            let arguments: Vec<_> = arguments.iter().map(for_kast).collect();
            match arguments.as_slice() {
                [] => Top { sort: sort.clone() },
                [argument] => argument.clone(),
                _ => And {
                    sort: sort.clone(),
                    arguments,
                },
            }
        }
        Or { sort, arguments } => {
            let arguments: Vec<_> = arguments.iter().map(for_kast).collect();
            match arguments.as_slice() {
                [] => Bottom { sort: sort.clone() },
                [argument] => argument.clone(),
                _ => Or {
                    sort: sort.clone(),
                    arguments,
                },
            }
        }
        Not { sort, argument } => Not {
            sort: sort.clone(),
            argument: child(argument),
        },
        Next { sort, argument } => Next {
            sort: sort.clone(),
            argument: child(argument),
        },
        Implies { sort, left, right } => Implies {
            sort: sort.clone(),
            left: child(left),
            right: child(right),
        },
        Iff { sort, left, right } => Iff {
            sort: sort.clone(),
            left: child(left),
            right: child(right),
        },
        Rewrites { sort, left, right } => Rewrites {
            sort: sort.clone(),
            left: child(left),
            right: child(right),
        },
        Exists {
            sort,
            variable,
            body,
        } => Exists {
            sort: sort.clone(),
            variable: variable.clone(),
            body: child(body),
        },
        Forall {
            sort,
            variable,
            body,
        } => Forall {
            sort: sort.clone(),
            variable: variable.clone(),
            body: child(body),
        },
        Mu { variable, body } => Mu {
            variable: variable.clone(),
            body: child(body),
        },
        Nu { variable, body } => Nu {
            variable: variable.clone(),
            body: child(body),
        },
        Ceil {
            operand_sort,
            result_sort,
            argument,
        } => Ceil {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: child(argument),
        },
        Floor {
            operand_sort,
            result_sort,
            argument,
        } => Floor {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: child(argument),
        },
        Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => Equals {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: child(left),
            right: child(right),
        },
        In {
            operand_sort,
            result_sort,
            left,
            right,
        } => In {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: child(left),
            right: child(right),
        },
        DomainValue { sort, value } => DomainValue {
            sort: sort.clone(),
            value: value.clone(),
        },
        AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => {
            let arguments: Vec<_> = arguments.iter().map(for_kast).collect();
            match associativity {
                Associativity::Left => {
                    let mut arguments = arguments.into_iter();
                    let first = arguments
                        .next()
                        .expect("associative patterns are non-empty");
                    arguments.fold(first, |left, right| Application {
                        symbol: symbol.clone(),
                        arguments: vec![left, right],
                    })
                }
                Associativity::Right => {
                    let (last, rest) = arguments
                        .split_last()
                        .expect("associative patterns are non-empty");
                    rest.iter()
                        .rev()
                        .cloned()
                        .fold(last.clone(), |right, left| Application {
                            symbol: symbol.clone(),
                            arguments: vec![left, right],
                        })
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::kore::parser::parse_pattern;

    use super::for_kast;

    #[test]
    fn collapses_connectives_only_when_requested() {
        let nullary = parse_pattern(r"\and{S}()").unwrap();
        let unary = parse_pattern(r"\or{S}(a{}())").unwrap();
        assert_eq!(for_kast(&nullary).to_string(), r"\top{S}()");
        assert_eq!(for_kast(&unary).to_string(), "a{}()");
    }

    #[test]
    fn expands_associative_nodes_and_preserves_sorts() {
        let left = parse_pattern(r"\left-assoc{}(f{S}(a{}(), b{}(), c{}()))").unwrap();
        let right = parse_pattern(r"\right-assoc{}(f{S}(a{}(), b{}(), c{}()))").unwrap();
        assert_eq!(
            for_kast(&left).to_string(),
            "f{S}(f{S}(a{}(), b{}()), c{}())"
        );
        assert_eq!(
            for_kast(&right).to_string(),
            "f{S}(a{}(), f{S}(b{}(), c{}()))"
        );
    }

    #[test]
    fn normalization_is_recursive_and_idempotent() {
        let pattern = parse_pattern(r"g{}(\and{S}(), \right-assoc{}(f{}(a{}(), b{}())))").unwrap();
        let normalized = for_kast(&pattern);
        assert_eq!(for_kast(&normalized), normalized);
    }
}
