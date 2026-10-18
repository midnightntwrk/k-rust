//! Matching-logic constructs in conditions.
//!
//! A condition whose root is a matching-logic connective (`#Or`, `#And`, `#Not`, `#Implies`,
//! `#Iff`, `#Top`, `#Bottom`, `#Ceil`, `#Floor`, `#Equals`, `#Exists`, `#Forall`) is a predicate,
//! not a Bool term. A pass that adds a conjunct to a condition must therefore conjoin a predicate
//! with the predicate conjunction `#And`: conjoined with `_andBool_`, a Bool function, the predicate
//! would stand as an argument of that function, where a connective denotes a set of values rather
//! than a truth, and where no backend reads it as a condition. Two Bool terms keep `_andBool_`, so
//! a condition without a connective compiles as before.
#![deny(clippy::wildcard_enum_match_arm)]

use crate::kast::{InternalLabel, Term};

/// The matching-logic connectives and predicate atoms of the frontend's term language.
const CONNECTIVES: [InternalLabel; 12] = [
    InternalLabel::Or,
    InternalLabel::And,
    InternalLabel::Not,
    InternalLabel::Implies,
    InternalLabel::Iff,
    InternalLabel::Top,
    InternalLabel::Bottom,
    InternalLabel::Ceil,
    InternalLabel::Floor,
    InternalLabel::Equals,
    InternalLabel::Exists,
    InternalLabel::Forall,
];

/// Whether the root of `term`, its annotations aside, is a matching-logic connective or predicate
/// atom.
pub(crate) fn is_ml_connective(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Apply { label, .. } if CONNECTIVES.iter().any(|connective| label.is(*connective))
    )
}

/// The conjunction of two conditions: the predicate `#And(left, right)` when either root is a
/// matching-logic connective, the Bool term `_andBool_(left, right)` otherwise.
pub(crate) fn conjoin_condition(left: Term, right: Term) -> Term {
    if is_ml_connective(&left) || is_ml_connective(&right) {
        Term::apply(InternalLabel::And.as_str(), vec![left, right])
    } else {
        Term::apply("_andBool_", vec![left, right])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test(name: &str) -> Term {
        Term::apply(name, vec![Term::variable("X")])
    }

    #[test]
    fn a_predicate_is_conjoined_as_a_predicate_and_two_bool_terms_as_a_bool_term() {
        let equals = Term::apply(
            InternalLabel::Equals.as_str(),
            vec![Term::variable("X"), Term::variable("Y")],
        );
        for (left, right) in [
            (equals.clone(), test("isInt")),
            (test("isInt"), equals.clone()),
            (equals.clone(), equals.clone()),
        ] {
            let conjoined = conjoin_condition(left, right);
            assert!(
                matches!(&conjoined, Term::Apply { label, .. } if label.is(InternalLabel::And)),
                "{conjoined:?}"
            );
        }
        let conjoined = conjoin_condition(test("isInt"), test("isBool"));
        assert!(
            matches!(&conjoined, Term::Apply { label, .. } if label.name == "_andBool_"),
            "{conjoined:?}"
        );
    }

    #[test]
    fn every_connective_and_only_a_connective_is_one() {
        for connective in CONNECTIVES {
            assert!(is_ml_connective(&Term::apply(
                connective.as_str(),
                Vec::new()
            )));
        }
        assert!(!is_ml_connective(&test("_andBool_")));
        assert!(!is_ml_connective(&Term::variable("X")));
        assert!(!is_ml_connective(&Term::apply(
            InternalLabel::Fun2.as_str(),
            Vec::new()
        )));
    }
}
