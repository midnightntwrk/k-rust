//! In-process evaluation of backend hooks implemented by Booster.

use num_bigint::{BigInt, Sign};

mod list;
mod map;

use crate::term::{Sort, SymbolType, Term, TermKind};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuiltinError {
    WrongArity {
        hook: String,
        expected: usize,
        actual: usize,
    },
    UnexpectedSort {
        hook: String,
        expected: Sort,
        actual: Sort,
    },
    AlternativeSortsDiffer {
        then_sort: Sort,
        else_sort: Sort,
    },
    IncompatibleMapSorts {
        left: Sort,
        right: Sort,
    },
}

/// Evaluate a hooked application, returning `None` when its arguments are not determined enough.
pub fn evaluate(term: &Term) -> Result<Option<Term>, BuiltinError> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return Ok(None);
    };
    let Some(hook) = symbol.attributes.hook.as_deref() else {
        return Ok(None);
    };
    evaluate_hook(hook, arguments)
}

pub fn evaluate_hook(hook: &str, arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    match hook {
        "BOOL.or" => bool_or(arguments),
        "BOOL.and" => bool_and(arguments),
        "BOOL.xor" => bool_binary(hook, arguments, |left, right| left != right),
        "BOOL.eq" => bool_binary(hook, arguments, |left, right| left == right),
        "BOOL.ne" => bool_binary(hook, arguments, |left, right| left != right),
        "BOOL.not" => bool_not(arguments),
        "BOOL.implies" => bool_implies(arguments),
        "INT.gt" => int_compare(hook, arguments, |left, right| left > right),
        "INT.ge" => int_compare(hook, arguments, |left, right| left >= right),
        "INT.eq" => int_compare(hook, arguments, |left, right| left == right),
        "INT.le" => int_compare(hook, arguments, |left, right| left <= right),
        "INT.lt" => int_compare(hook, arguments, |left, right| left < right),
        "INT.ne" => int_compare(hook, arguments, |left, right| left != right),
        "INT.add" => int_binary(hook, arguments, |left, right| left + right),
        "INT.sub" => int_binary(hook, arguments, |left, right| left - right),
        "INT.mul" => int_binary(hook, arguments, |left, right| left * right),
        "INT.abs" => int_abs(arguments),
        "KEQUAL.ite" => kequal_ite(arguments),
        "KEQUAL.eq" => kequal(arguments, false),
        "KEQUAL.ne" => kequal(arguments, true),
        hook if hook.starts_with("LIST.") => list::evaluate(hook, arguments),
        hook if hook.starts_with("MAP.") => map::evaluate(hook, arguments),
        _ => Ok(None),
    }
}

fn bool_or(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("BOOL.or", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    Ok(match (read_bool(left), read_bool(right)) {
        (Some(true), _) | (_, Some(true)) => Some(bool_term(true)),
        (Some(false), Some(false)) => Some(bool_term(false)),
        _ => None,
    })
}

fn bool_and(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("BOOL.and", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    Ok(match (read_bool(left), read_bool(right)) {
        (Some(false), _) | (_, Some(false)) => Some(bool_term(false)),
        (Some(true), Some(true)) => Some(bool_term(true)),
        _ => None,
    })
}

fn bool_binary(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(bool, bool) -> bool,
) -> Result<Option<Term>, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    Ok(read_bool(left)
        .zip(read_bool(right))
        .map(|(left, right)| bool_term(operation(left, right))))
}

fn bool_not(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("BOOL.not", arguments, 1)?;
    Ok(read_bool(&arguments[0]).map(|value| bool_term(!value)))
}

fn bool_implies(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("BOOL.implies", arguments, 2)?;
    let [left, right] = arguments else {
        unreachable!()
    };
    Ok(match (read_bool(left), read_bool(right)) {
        (Some(false), _) => Some(bool_term(true)),
        (Some(true), Some(right)) => Some(bool_term(right)),
        _ => None,
    })
}

fn int_compare(
    hook: &str,
    arguments: &[Term],
    comparison: impl FnOnce(&BigInt, &BigInt) -> bool,
) -> Result<Option<Term>, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    Ok(read_int(&arguments[0])
        .zip(read_int(&arguments[1]))
        .map(|(left, right)| bool_term(comparison(&left, &right))))
}

fn int_binary(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(BigInt, BigInt) -> BigInt,
) -> Result<Option<Term>, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    Ok(read_int(&arguments[0])
        .zip(read_int(&arguments[1]))
        .map(|(left, right)| int_term(operation(left, right))))
}

fn int_abs(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("INT.abs", arguments, 1)?;
    Ok(read_int(&arguments[0]).map(|value| {
        if value.sign() == Sign::Minus {
            int_term(-value)
        } else {
            int_term(value)
        }
    }))
}

fn kequal_ite(arguments: &[Term]) -> Result<Option<Term>, BuiltinError> {
    expect_arity("KEQUAL.ite", arguments, 3)?;
    let [condition, then_value, else_value] = arguments else {
        unreachable!()
    };
    expect_sort("KEQUAL.ite", condition, &Sort::simple("SortBool"))?;
    if then_value.sort() != else_value.sort() {
        return Err(BuiltinError::AlternativeSortsDiffer {
            then_sort: then_value.sort(),
            else_sort: else_value.sort(),
        });
    }
    Ok(match read_bool(condition) {
        Some(true) => Some(then_value.clone()),
        Some(false) => Some(else_value.clone()),
        None => None,
    })
}

fn kequal(arguments: &[Term], negate: bool) -> Result<Option<Term>, BuiltinError> {
    expect_arity(if negate { "KEQUAL.ne" } else { "KEQUAL.eq" }, arguments, 2)?;
    let Some(left) = k_sequence_item(&arguments[0]) else {
        return Ok(None);
    };
    let Some(right) = k_sequence_item(&arguments[1]) else {
        return Ok(None);
    };
    Ok(evaluate_equality(left, right).map(|equal| bool_term(equal != negate)))
}

fn evaluate_equality(left: &Term, right: &Term) -> Option<bool> {
    match (left.kind(), right.kind()) {
        (
            TermKind::Application {
                symbol: left_symbol,
                sort_arguments: left_sorts,
                arguments: left_arguments,
            },
            TermKind::Application {
                symbol: right_symbol,
                sort_arguments: right_sorts,
                arguments: right_arguments,
            },
        ) if is_constructor(left_symbol) && is_constructor(right_symbol) => {
            if left_symbol != right_symbol
                || left_sorts != right_sorts
                || left_arguments.len() != right_arguments.len()
            {
                return Some(false);
            }
            let mut equal = true;
            for (left, right) in left_arguments.iter().zip(right_arguments) {
                equal &= evaluate_equality(left, right)?;
            }
            Some(equal)
        }
        (TermKind::Application { symbol, .. }, right)
            if is_constructor(symbol) && is_rigid_non_application(right) =>
        {
            Some(false)
        }
        (left, TermKind::Application { symbol, .. })
            if is_constructor(symbol) && is_rigid_non_application(left) =>
        {
            Some(false)
        }
        (
            TermKind::Injection {
                source: left_source,
                target: left_target,
                term: left,
            },
            TermKind::Injection {
                source: right_source,
                target: right_target,
                term: right,
            },
        ) if left_source == right_source && left_target == right_target => {
            evaluate_equality(left, right)
        }
        (TermKind::DomainValue { .. }, TermKind::DomainValue { .. }) => Some(left == right),
        _ if left == right => Some(true),
        _ => None,
    }
}

fn k_sequence_item(term: &Term) -> Option<&Term> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    let [first, tail] = arguments.as_slice() else {
        return None;
    };
    let TermKind::Injection { term: item, .. } = first.kind() else {
        return None;
    };
    let TermKind::Application {
        symbol: tail_symbol,
        arguments: tail_arguments,
        ..
    } = tail.kind()
    else {
        return None;
    };
    (symbol.name.as_ref() == "kseq"
        && tail_symbol.name.as_ref() == "dotk"
        && tail_arguments.is_empty())
    .then_some(item)
}

fn read_bool(term: &Term) -> Option<bool> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    if sort != &Sort::simple("SortBool") {
        return None;
    }
    match value.as_ref() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

pub(super) fn read_int(term: &Term) -> Option<BigInt> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    (sort == &Sort::simple("SortInt"))
        .then(|| value.parse().ok())
        .flatten()
}

pub(super) fn bool_term(value: bool) -> Term {
    Term::domain_value(
        Sort::simple("SortBool"),
        if value { "true" } else { "false" },
    )
}

pub(super) fn int_term(value: BigInt) -> Term {
    Term::domain_value(Sort::simple("SortInt"), value.to_string())
}

pub(super) fn expect_arity(
    hook: &str,
    arguments: &[Term],
    expected: usize,
) -> Result<(), BuiltinError> {
    if arguments.len() == expected {
        Ok(())
    } else {
        Err(BuiltinError::WrongArity {
            hook: hook.into(),
            expected,
            actual: arguments.len(),
        })
    }
}

pub(super) fn expect_sort(hook: &str, term: &Term, expected: &Sort) -> Result<(), BuiltinError> {
    let actual = term.sort();
    if &actual == expected {
        Ok(())
    } else {
        Err(BuiltinError::UnexpectedSort {
            hook: hook.into(),
            expected: expected.clone(),
            actual,
        })
    }
}

fn is_constructor(symbol: &crate::term::Symbol) -> bool {
    symbol.attributes.symbol_type == SymbolType::Constructor
}

fn is_rigid_non_application(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::DomainValue { .. }
            | TermKind::Injection { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. }
    )
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::term::{FunctionType, Symbol, SymbolAttributes, Variable};

    fn hooked(hook: &str, result_sort: Sort, arguments: Vec<Term>) -> Term {
        let argument_sorts = arguments.iter().map(Term::sort).collect();
        Term::application(
            Arc::new(Symbol {
                name: format!("hook-{hook}").into(),
                sort_variables: Vec::new(),
                argument_sorts,
                result_sort,
                attributes: SymbolAttributes {
                    symbol_type: SymbolType::Function(FunctionType::Total),
                    associative: false,
                    idempotent: false,
                    macro_or_alias: false,
                    has_evaluators: true,
                    smt: None,
                    hook: Some(hook.into()),
                    collection: None,
                },
            }),
            Vec::new(),
            arguments,
        )
    }

    #[test]
    fn boolean_hooks_short_circuit_unknown_arguments() {
        let unknown = Term::variable(Variable::new("B", Sort::simple("SortBool")));
        let false_and_unknown = hooked(
            "BOOL.and",
            Sort::simple("SortBool"),
            vec![bool_term(false), unknown.clone()],
        );
        let true_and_unknown = hooked(
            "BOOL.and",
            Sort::simple("SortBool"),
            vec![bool_term(true), unknown],
        );

        assert_eq!(evaluate(&false_and_unknown), Ok(Some(bool_term(false))));
        assert_eq!(evaluate(&true_and_unknown), Ok(None));
    }

    #[test]
    fn integer_hooks_preserve_arbitrary_precision() {
        let left = BigInt::parse_bytes(b"99999999999999999999999999999999999999", 10).unwrap();
        let right = BigInt::from(2);
        let addition = hooked(
            "INT.add",
            Sort::simple("SortInt"),
            vec![int_term(left.clone()), int_term(right.clone())],
        );
        let comparison = hooked(
            "INT.gt",
            Sort::simple("SortBool"),
            vec![int_term(left.clone()), int_term(right)],
        );

        assert_eq!(evaluate(&addition), Ok(Some(int_term(left + 2))));
        assert_eq!(evaluate(&comparison), Ok(Some(bool_term(true))));
    }

    #[test]
    fn reports_wrong_builtin_arity() {
        let term = hooked(
            "INT.add",
            Sort::simple("SortInt"),
            vec![int_term(BigInt::from(1))],
        );

        assert_eq!(
            evaluate(&term),
            Err(BuiltinError::WrongArity {
                hook: "INT.add".into(),
                expected: 2,
                actual: 1,
            })
        );
    }
}
