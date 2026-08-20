//! Deterministic `STRING` hooks implemented by Kore's fallback evaluator.

use num_bigint::BigInt;
use num_traits::ToPrimitive;

use super::{BuiltinError, BuiltinResult, bool_term, expect_arity, int_term, read_int};
use crate::term::{Sort, Term, TermKind};

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    match hook {
        "STRING.eq" => compare(hook, arguments, |left, right| left == right),
        "STRING.ne" => compare(hook, arguments, |left, right| left != right),
        "STRING.lt" => compare(hook, arguments, |left, right| left < right),
        "STRING.le" => compare(hook, arguments, |left, right| left <= right),
        "STRING.gt" => compare(hook, arguments, |left, right| left > right),
        "STRING.ge" => compare(hook, arguments, |left, right| left >= right),
        "STRING.concat" => concatenate(arguments),
        "STRING.substr" => substring(arguments),
        "STRING.length" => length(arguments),
        "STRING.find" => find(arguments),
        "STRING.string2base" => string_to_base(arguments),
        "STRING.base2string" => base_to_string(arguments),
        "STRING.string2int" => string_to_int(arguments),
        "STRING.int2string" => int_to_string(arguments),
        "STRING.chr" => chr(arguments),
        "STRING.ord" => ord(arguments),
        "STRING.token2string" => token_to_string(arguments),
        _ => Ok(BuiltinResult::NotApplicable),
    }
}

fn compare(
    hook: &str,
    arguments: &[Term],
    comparison: impl FnOnce(&str, &str) -> bool,
) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let Some((left, right)) = read_string(&arguments[0]).zip(read_string(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(bool_term(comparison(left, right))))
}

fn concatenate(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.concat", arguments, 2)?;
    let Some((left, right)) = read_string(&arguments[0]).zip(read_string(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(format!("{left}{right}"))))
}

fn substring(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.substr", arguments, 3)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((start, end)) = read_int(&arguments[1]).zip(read_int(&arguments[2])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((start, end)) = start.to_i64().zip(end.to_i64()) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let start = usize::try_from(start.max(0)).unwrap_or(usize::MAX);
    let count = usize::try_from(end.max(0))
        .unwrap_or(usize::MAX)
        .saturating_sub(start);
    let result = value.chars().skip(start).take(count).collect::<String>();
    Ok(BuiltinResult::Value(string_term(result)))
}

fn length(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.length", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        value.chars().count(),
    ))))
}

fn find(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.find", arguments, 3)?;
    let Some((haystack, needle)) = read_string(&arguments[0]).zip(read_string(&arguments[1]))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(start) = read_int(&arguments[2]).and_then(|start| start.to_i64()) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let haystack = haystack.chars().collect::<Vec<_>>();
    let needle = needle.chars().collect::<Vec<_>>();
    let start = usize::try_from(start.max(0)).unwrap_or(usize::MAX);
    let found = if needle.is_empty() {
        (start <= haystack.len()).then_some(start)
    } else {
        haystack
            .get(start..)
            .and_then(|tail| {
                tail.windows(needle.len())
                    .position(|window| window == needle)
            })
            .map(|offset| start + offset)
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        found
            .and_then(|index| i64::try_from(index).ok())
            .unwrap_or(-1),
    ))))
}

fn string_to_base(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.string2base", arguments, 2)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(base) = read_base(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BigInt::parse_bytes(value.as_bytes(), base)
        .map(int_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

fn base_to_string(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.base2string", arguments, 2)?;
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(base) = read_base(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(value.to_str_radix(base))))
}

fn string_to_int(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.string2int", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(value
        .parse::<BigInt>()
        .ok()
        .map(int_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

fn int_to_string(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.int2string", arguments, 1)?;
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(value.to_string())))
}

fn chr(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.chr", arguments, 1)?;
    let Some(value) = read_int(&arguments[0]).and_then(|value| value.to_u32()) else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(char::from_u32(value)
        .map(|value| string_term(value.to_string()))
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

fn ord(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.ord", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut characters = value.chars();
    let Some(character) = characters.next() else {
        return Ok(BuiltinResult::Bottom);
    };
    if characters.next().is_some() {
        return Ok(BuiltinResult::Bottom);
    }
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        character as u32,
    ))))
}

fn token_to_string(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.token2string", arguments, 1)?;
    let TermKind::DomainValue { value, .. } = arguments[0].kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(value.as_ref())))
}

fn read_base(term: &Term) -> Option<u32> {
    read_int(term)
        .and_then(|base| base.to_u32())
        .filter(|base| (2..=36).contains(base))
}

fn read_string(term: &Term) -> Option<&str> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    (sort == &Sort::simple("SortString")).then_some(value.as_ref())
}

fn string_term(value: impl Into<String>) -> Term {
    Term::domain_value(Sort::simple("SortString"), value.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn evaluate(hook: &str, arguments: Vec<Term>) -> BuiltinResult {
        super::evaluate(hook, &arguments).unwrap()
    }

    #[test]
    fn evaluates_unicode_string_operations_by_code_point() {
        assert_eq!(
            evaluate("STRING.length", vec![string_term("a🦀é")]),
            BuiltinResult::Value(int_term(BigInt::from(3)))
        );
        assert_eq!(
            evaluate(
                "STRING.substr",
                vec![string_term("a🦀é"), int_term(1.into()), int_term(3.into())]
            ),
            BuiltinResult::Value(string_term("🦀é"))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![string_term("a🦀é🦀"), string_term("🦀"), int_term(2.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(3)))
        );
    }

    #[test]
    fn converts_strings_in_decimal_and_explicit_bases() {
        assert_eq!(
            evaluate("STRING.string2int", vec![string_term("-42")]),
            BuiltinResult::Value(int_term(BigInt::from(-42)))
        );
        assert_eq!(
            evaluate(
                "STRING.string2base",
                vec![string_term("-ff"), int_term(16.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(-255)))
        );
        assert_eq!(
            evaluate(
                "STRING.base2string",
                vec![int_term((-255).into()), int_term(16.into())]
            ),
            BuiltinResult::Value(string_term("-ff"))
        );
        assert_eq!(
            evaluate("STRING.string2int", vec![string_term("4x")]),
            BuiltinResult::Bottom
        );
    }

    #[test]
    fn converts_unicode_scalar_values() {
        assert_eq!(
            evaluate("STRING.chr", vec![int_term(0x1f980.into())]),
            BuiltinResult::Value(string_term("🦀"))
        );
        assert_eq!(
            evaluate("STRING.ord", vec![string_term("🦀")]),
            BuiltinResult::Value(int_term(BigInt::from(0x1f980)))
        );
        assert_eq!(
            evaluate("STRING.ord", vec![string_term("ab")]),
            BuiltinResult::Bottom
        );
    }
}
