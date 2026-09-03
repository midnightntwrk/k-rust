//! Explicit semantic normalization for consumers such as KORE-to-KAST conversion.

use super::ast::{Associativity, Pattern};

/// Converts syntax-preserving KORE into the shape expected at the KAST boundary.
///
/// Empty and unary conjunctions/disjunctions follow scala-kore's builders, and
/// associative wrappers become binary application trees. Unlike pyk's current
/// `RightAssoc.pattern`, symbol sort parameters are preserved in both directions.
pub fn for_kast(pattern: &Pattern) -> Pattern {
    use Pattern::*;
    super::walk::rebuild(pattern, |pattern, arguments| match pattern {
        And { sort, .. } => match arguments.len() {
            0 => Top { sort: sort.clone() },
            1 => arguments
                .into_iter()
                .next()
                .expect("one normalized conjunction argument is present"),
            _ => And {
                sort: sort.clone(),
                arguments,
            },
        },
        Or { sort, .. } => match arguments.len() {
            0 => Bottom { sort: sort.clone() },
            1 => arguments
                .into_iter()
                .next()
                .expect("one normalized disjunction argument is present"),
            _ => Or {
                sort: sort.clone(),
                arguments,
            },
        },
        AssociativeApplication {
            associativity,
            symbol,
            ..
        } => match associativity {
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
                let mut arguments = arguments.into_iter().rev();
                let last = arguments
                    .next()
                    .expect("associative patterns are non-empty");
                arguments.fold(last, |right, left| Application {
                    symbol: symbol.clone(),
                    arguments: vec![left, right],
                })
            }
        },
        _ => super::walk::clone_node(pattern, arguments),
    })
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
