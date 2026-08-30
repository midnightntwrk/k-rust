//! In-process evaluation of backend hooks implemented by Booster.

use num_bigint::{BigInt, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};

mod bytes;
mod float;
mod krypto;
mod list;
mod map;
mod set;
mod string;

use crate::{
    term::{Sort, SymbolType, Term, TermKind},
    timeout::interruption_requested,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuiltinError {
    Interrupted,
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
    InvalidFloatToken {
        hook: String,
        token: String,
    },
    UnsupportedFloatFormat {
        hook: String,
        precision: u32,
        exponent_bits: u32,
    },
    MismatchedFloatFormats {
        hook: String,
        left_precision: u32,
        left_exponent_bits: u32,
        right_precision: u32,
        right_exponent_bits: u32,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuiltinResult {
    NotApplicable,
    Value(Term),
    Bottom,
    Effect(BuiltinEffect),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuiltinEffect {
    UserLog(String),
}

impl From<Option<Term>> for BuiltinResult {
    fn from(value: Option<Term>) -> Self {
        value.map_or(Self::NotApplicable, Self::Value)
    }
}

/// Evaluate a hooked application, returning `None` when its arguments are not determined enough.
pub fn evaluate(term: &Term) -> Result<BuiltinResult, BuiltinError> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(hook) = symbol.attributes.hook.as_deref() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let result_sort = term.sort();
    evaluate_hook_with_sort(hook, arguments, Some(&result_sort))
}

/// Hook namespaces this backend dispatches beyond K's fixed builtin set.
///
/// Java K only treats these plugin namespaces as hooked when `kompile --hook-namespaces` names
/// them; the Rust backend implements them natively, so KORE emitted for it admits them by default.
pub const PLUGIN_HOOK_NAMESPACES: [&str; 3] = ["KRYPTO", "HASH", "SECP256K1"];

pub fn evaluate_hook(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    evaluate_hook_with_sort(hook, arguments, None)
}

fn evaluate_hook_with_sort(
    hook: &str,
    arguments: &[Term],
    result_sort: Option<&Sort>,
) -> Result<BuiltinResult, BuiltinError> {
    check_interrupted()?;
    match hook {
        "INT.ediv" => return int_partial_binary(hook, arguments, euclidean_division),
        "INT.emod" => return int_partial_binary(hook, arguments, euclidean_modulus),
        "INT.tdiv" => return int_partial_binary(hook, arguments, truncating_division),
        "INT.tmod" => return int_partial_binary(hook, arguments, truncating_modulus),
        "INT.pow" => return int_pow(arguments),
        "INT.powmod" => return int_powmod(arguments),
        "INT.log2" => return int_log2(arguments),
        _ => {}
    }
    let result = match hook {
        "BOOL.or" => bool_or(arguments),
        "BOOL.orElse" => bool_or(arguments),
        "BOOL.and" => bool_and(arguments),
        "BOOL.andThen" => bool_and(arguments),
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
        "INT.min" => int_binary(hook, arguments, std::cmp::min),
        "INT.max" => int_binary(hook, arguments, std::cmp::max),
        "INT.and" => int_binary(hook, arguments, |left, right| left & right),
        "INT.or" => int_binary(hook, arguments, |left, right| left | right),
        "INT.xor" => int_binary(hook, arguments, |left, right| left ^ right),
        "INT.not" => int_unary(hook, arguments, |value| !value),
        "INT.shl" => int_shift(hook, arguments, false),
        "INT.shr" => int_shift(hook, arguments, true),
        "KEQUAL.ite" => kequal_ite(arguments),
        "KEQUAL.eq" => kequal(arguments, false),
        "KEQUAL.ne" => kequal(arguments, true),
        "IO.logString" => return io_log_string(arguments),
        hook if hook.starts_with("LIST.") => return list::evaluate(hook, arguments),
        hook if hook.starts_with("MAP.") => return map::evaluate(hook, arguments),
        hook if hook.starts_with("SET.") => set::evaluate(hook, arguments),
        hook if hook.starts_with("BYTES.") => return bytes::evaluate(hook, arguments),
        hook if hook.starts_with("FLOAT.") => return float::evaluate(hook, arguments),
        hook if hook
            .split_once('.')
            .is_some_and(|(namespace, _)| PLUGIN_HOOK_NAMESPACES.contains(&namespace)) =>
        {
            return krypto::evaluate(hook, arguments);
        }
        hook if hook.starts_with("STRING.") => {
            return string::evaluate(hook, arguments, result_sort);
        }
        _ => Ok(None),
    }?;
    Ok(result.into())
}

fn check_interrupted() -> Result<(), BuiltinError> {
    if interruption_requested() {
        Err(BuiltinError::Interrupted)
    } else {
        Ok(())
    }
}

fn io_log_string(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("IO.logString", arguments, 1)?;
    let TermKind::DomainValue { sort, value } = arguments[0].kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if sort != &Sort::simple("SortString") {
        return Ok(BuiltinResult::NotApplicable);
    }
    Ok(BuiltinResult::Effect(BuiltinEffect::UserLog(
        value.to_string(),
    )))
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

fn int_unary(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(BigInt) -> BigInt,
) -> Result<Option<Term>, BuiltinError> {
    expect_arity(hook, arguments, 1)?;
    Ok(read_int(&arguments[0]).map(|value| int_term(operation(value))))
}

fn int_partial_binary(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(BigInt, BigInt) -> Option<BigInt>,
) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let Some((left, right)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(operation(left, right)
        .map(int_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

fn truncating_division(left: BigInt, right: BigInt) -> Option<BigInt> {
    (!right.is_zero()).then(|| left / right)
}

fn truncating_modulus(left: BigInt, right: BigInt) -> Option<BigInt> {
    (!right.is_zero()).then(|| left % right)
}

fn euclidean_modulus(left: BigInt, right: BigInt) -> Option<BigInt> {
    if right.is_zero() {
        return None;
    }
    let modulus = right.abs();
    let remainder = left % &modulus;
    Some(if remainder.sign() == Sign::Minus {
        remainder + modulus
    } else {
        remainder
    })
}

fn euclidean_division(left: BigInt, right: BigInt) -> Option<BigInt> {
    let remainder = euclidean_modulus(left.clone(), right.clone())?;
    Some((left - remainder) / right)
}

fn int_pow(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("INT.pow", arguments, 2)?;
    let Some((mut base, exponent)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if exponent.sign() == Sign::Minus {
        return Ok(BuiltinResult::Bottom);
    }
    let Some(mut exponent) = exponent.to_u32() else {
        return Ok(BuiltinResult::Bottom);
    };
    let mut result = BigInt::one();
    while exponent != 0 {
        check_interrupted()?;
        if exponent & 1 == 1 {
            result *= &base;
        }
        exponent >>= 1;
        if exponent != 0 {
            base = &base * &base;
        }
    }
    Ok(BuiltinResult::Value(int_term(result)))
}

fn int_powmod(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("INT.powmod", arguments, 3)?;
    let Some((base, exponent, modulus)) = read_int(&arguments[0])
        .zip(read_int(&arguments[1]))
        .zip(read_int(&arguments[2]))
        .map(|((base, exponent), modulus)| (base, exponent, modulus))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if modulus.is_zero() {
        return Ok(BuiltinResult::Bottom);
    }
    let modulus = modulus.abs();
    let (base, exponent) = if exponent.sign() == Sign::Minus {
        let Some(inverse) = modular_inverse(&base, &modulus)? else {
            return Ok(BuiltinResult::Bottom);
        };
        (inverse, -exponent)
    } else {
        (base, exponent)
    };
    let mut base = euclidean_modulus(base, modulus.clone()).expect("non-zero modulus");
    let mut exponent = exponent;
    let mut result = BigInt::one();
    while !exponent.is_zero() {
        check_interrupted()?;
        if (&exponent & BigInt::one()) == BigInt::one() {
            result = (result * &base) % &modulus;
        }
        exponent >>= 1;
        if !exponent.is_zero() {
            base = (&base * &base) % &modulus;
        }
    }
    Ok(BuiltinResult::Value(int_term(result % modulus)))
}

fn modular_inverse(value: &BigInt, modulus: &BigInt) -> Result<Option<BigInt>, BuiltinError> {
    let (mut old_r, mut r) = (value.clone(), modulus.clone());
    let (mut old_s, mut s) = (BigInt::one(), BigInt::zero());
    while !r.is_zero() {
        check_interrupted()?;
        let quotient = &old_r / &r;
        (old_r, r) = (r.clone(), old_r - &quotient * r);
        (old_s, s) = (s.clone(), old_s - quotient * s);
    }
    if old_r.abs() != BigInt::one() {
        return Ok(None);
    }
    if old_r.sign() == Sign::Minus {
        old_s = -old_s;
    }
    Ok(euclidean_modulus(old_s, modulus.clone()))
}

fn int_log2(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("INT.log2", arguments, 1)?;
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if value <= BigInt::zero() {
        return Ok(BuiltinResult::Bottom);
    }
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        value.bits() - 1,
    ))))
}

fn int_shift(hook: &str, arguments: &[Term], right: bool) -> Result<Option<Term>, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let Some((value, amount)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) else {
        return Ok(None);
    };
    let amount = if right { -amount } else { amount };
    let magnitude = amount.abs().to_usize();
    Ok(magnitude.map(|magnitude| {
        int_term(if amount.sign() == Sign::Minus {
            value >> magnitude
        } else {
            value << magnitude
        })
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

pub(crate) fn k_sequence_item(term: &Term) -> Option<&Term> {
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
    use std::{sync::Arc, time::Duration};

    use super::*;
    use crate::{
        term::{FunctionType, Symbol, SymbolAttributes, Variable},
        timeout::{StepTimeoutController, StepTimeoutOptions},
    };

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
                    injective: false,
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

        assert_eq!(
            evaluate(&false_and_unknown),
            Ok(BuiltinResult::Value(bool_term(false)))
        );
        assert_eq!(
            evaluate(&true_and_unknown),
            Ok(BuiltinResult::NotApplicable)
        );
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

        assert_eq!(
            evaluate(&addition),
            Ok(BuiltinResult::Value(int_term(left + 2)))
        );
        assert_eq!(
            evaluate(&comparison),
            Ok(BuiltinResult::Value(bool_term(true)))
        );
    }

    #[test]
    fn string_to_token_uses_the_application_result_sort() {
        let token_sort = Sort::simple("SortIdentifier");
        let application = hooked(
            "STRING.string2token",
            token_sort.clone(),
            vec![Term::domain_value(Sort::simple("SortString"), "alpha")],
        );

        assert_eq!(
            evaluate(&application),
            Ok(BuiltinResult::Value(Term::domain_value(
                token_sort, "alpha"
            )))
        );
    }

    fn evaluate_int(hook: &str, arguments: &[i64]) -> BuiltinResult {
        evaluate_hook(
            hook,
            &arguments
                .iter()
                .copied()
                .map(BigInt::from)
                .map(int_term)
                .collect::<Vec<_>>(),
        )
        .unwrap()
    }

    fn float_term(value: &str) -> Term {
        Term::domain_value(Sort::simple("SortFloat"), value)
    }

    #[test]
    fn float_representation_hooks_use_canonical_k_tokens() {
        let cases = [
            (
                "FLOAT.precision",
                vec![float_term("0.1f")],
                BuiltinResult::Value(int_term(BigInt::from(24))),
            ),
            (
                "FLOAT.exponentBits",
                vec![float_term("0.1p53x11")],
                BuiltinResult::Value(int_term(BigInt::from(11))),
            ),
            (
                "FLOAT.sign",
                vec![float_term("-0.0p24x8")],
                BuiltinResult::Value(bool_term(true)),
            ),
            (
                "FLOAT.isNaN",
                vec![float_term("NaNp53x11")],
                BuiltinResult::Value(bool_term(true)),
            ),
            (
                "FLOAT.neg",
                vec![float_term("0.1")],
                BuiltinResult::Value(float_term("-1.0000000000000001e-01p53x11")),
            ),
            (
                "FLOAT.neg",
                vec![float_term("0.1f")],
                BuiltinResult::Value(float_term("-1.00000001e-01p24x8")),
            ),
            (
                "FLOAT.neg",
                vec![float_term("0.0f")],
                BuiltinResult::Value(float_term("-0e+00p24x8")),
            ),
            (
                "FLOAT.neg",
                vec![float_term("-Infinity")],
                BuiltinResult::Value(float_term("Infinityp53x11")),
            ),
        ];

        for (hook, arguments, expected) in cases {
            assert_eq!(evaluate_hook(hook, &arguments), Ok(expected), "{hook}");
        }
    }

    #[test]
    fn float_tokens_reject_unsupported_or_malformed_ground_formats() {
        assert_eq!(
            evaluate_hook("FLOAT.precision", &[float_term("1.0p2x8")]),
            Err(BuiltinError::UnsupportedFloatFormat {
                hook: "FLOAT.precision".into(),
                precision: 2,
                exponent_bits: 8,
            })
        );
        assert_eq!(
            evaluate_hook("FLOAT.sign", &[float_term("not-a-float")]),
            Err(BuiltinError::InvalidFloatToken {
                hook: "FLOAT.sign".into(),
                token: "not-a-float".into(),
            })
        );

        let symbolic = Term::variable(Variable::new("F", Sort::simple("SortFloat")));
        assert_eq!(
            evaluate_hook("FLOAT.sign", &[symbolic]),
            Ok(BuiltinResult::NotApplicable)
        );
    }

    #[test]
    fn integer_fallback_hooks_match_kore_arithmetic() {
        let cases = [
            ("INT.tdiv", &[-5, -3][..], 1),
            ("INT.tmod", &[-5, -3][..], -2),
            ("INT.ediv", &[-5, -3][..], 2),
            ("INT.emod", &[-5, -3][..], 1),
            ("INT.pow", &[2, 10][..], 1_024),
            ("INT.powmod", &[3, -1, 7][..], 5),
            ("INT.log2", &[1_024][..], 10),
            ("INT.and", &[6, 3][..], 2),
            ("INT.or", &[4, 3][..], 7),
            ("INT.xor", &[6, 3][..], 5),
            ("INT.shl", &[3, 4][..], 48),
            ("INT.shr", &[-16, 2][..], -4),
            ("INT.min", &[-2, 3][..], -2),
            ("INT.max", &[-2, 3][..], 3),
        ];
        for (hook, arguments, expected) in cases {
            assert_eq!(
                evaluate_int(hook, arguments),
                BuiltinResult::Value(int_term(BigInt::from(expected))),
                "{hook}"
            );
        }
        assert_eq!(
            evaluate_int("INT.not", &[0]),
            BuiltinResult::Value(int_term(BigInt::from(-1)))
        );
    }

    #[test]
    fn undefined_integer_operations_are_bottom() {
        assert_eq!(evaluate_int("INT.ediv", &[1, 0]), BuiltinResult::Bottom);
        assert_eq!(evaluate_int("INT.pow", &[2, -1]), BuiltinResult::Bottom);
        assert_eq!(evaluate_int("INT.log2", &[0]), BuiltinResult::Bottom);
        assert_eq!(
            evaluate_int("INT.powmod", &[2, -1, 4]),
            BuiltinResult::Bottom
        );
    }

    #[test]
    fn native_hooks_observe_the_active_step_deadline() {
        let controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        let _timer = controller.begin_step();

        assert_eq!(
            evaluate_hook("INT.pow", &[int_term(2.into()), int_term(10.into())]),
            Err(BuiltinError::Interrupted)
        );
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

    #[test]
    fn krypto_wrong_arity_is_an_error_not_a_fallthrough() {
        let dummy = Term::domain_value(Sort::simple("SortBytes"), "");
        let cases = [
            ("KRYPTO.keccak256", 1),
            ("HASH.keccak256", 1),
            ("KRYPTO.keccak256raw", 1),
            ("KRYPTO.sha256", 1),
            ("HASH.sha256", 1),
            ("KRYPTO.sha3256", 1),
            ("HASH.sha3_256", 1),
            ("KRYPTO.sha512_256raw", 1),
            ("KRYPTO.ripemd160", 1),
            ("HASH.ripemd160", 1),
            ("KRYPTO.ecdsaPubKey", 1),
            ("KRYPTO.ecdsaRecover", 4),
            ("SECP256K1.ecdsaRecover", 4),
        ];

        for (hook, expected) in cases {
            let arguments = vec![dummy.clone(); expected + 1];
            assert_eq!(
                evaluate_hook(hook, &arguments),
                Err(BuiltinError::WrongArity {
                    hook: hook.into(),
                    expected,
                    actual: expected + 1,
                }),
                "{hook}"
            );
        }
    }

    #[test]
    fn raw_hash_hooks_are_evaluated_through_the_public_dispatcher() {
        let empty = bytes::bytes_term(&[]);

        for hook in ["KRYPTO.sha256raw", "KRYPTO.ripemd160raw"] {
            assert!(
                matches!(
                    evaluate_hook(hook, std::slice::from_ref(&empty)),
                    Ok(BuiltinResult::Value(_))
                ),
                "{hook}"
            );
        }
    }

    #[test]
    fn bn128_validity_hooks_are_registered_with_the_public_evaluator() {
        let dummy = Term::domain_value(Sort::simple("SortCapabilityAuditDummy"), "dummy");

        for hook in ["KRYPTO.bn128valid", "KRYPTO.bn128g2valid"] {
            assert_eq!(
                evaluate_hook(hook, &[dummy.clone(), dummy.clone()]),
                Err(BuiltinError::WrongArity {
                    hook: hook.into(),
                    expected: 1,
                    actual: 2,
                }),
                "{hook}"
            );
        }
    }

    #[test]
    fn bn128_arithmetic_hooks_are_registered_with_the_public_evaluator() {
        let dummy = Term::domain_value(Sort::simple("SortCapabilityAuditDummy"), "dummy");

        for hook in ["KRYPTO.bn128add", "KRYPTO.bn128mul"] {
            let arguments = vec![dummy.clone(); 3];
            assert_eq!(
                evaluate_hook(hook, &arguments),
                Err(BuiltinError::WrongArity {
                    hook: hook.into(),
                    expected: 2,
                    actual: 3,
                }),
                "{hook}"
            );
        }
    }

    #[test]
    fn bn128_pairing_hook_is_registered_with_the_public_evaluator() {
        let dummy = Term::domain_value(Sort::simple("SortCapabilityAuditDummy"), "dummy");
        let arguments = vec![dummy; 3];

        assert_eq!(
            evaluate_hook("KRYPTO.bn128ate", &arguments),
            Err(BuiltinError::WrongArity {
                hook: "KRYPTO.bn128ate".into(),
                expected: 2,
                actual: 3,
            })
        );
    }
}
