//! Deterministic `STRING` hooks implemented by Kore's fallback evaluator.

use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

use super::{
    BuiltinError, BuiltinResult, UnsupportedHookReason, bool_term, check_interrupted, expect_arity,
    int_term, read_int,
};
use crate::term::{Sort, Term, TermKind};

pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    result_sort: Option<&Sort>,
) -> Result<BuiltinResult, BuiltinError> {
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
        "STRING.string2token" => string_to_token(arguments, result_sort),
        _ => Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        )),
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
    let start = saturating_i64(&start);
    let end = saturating_i64(&end);
    let start_index = usize::try_from(start.max(0)).unwrap_or(usize::MAX);
    let count = usize::try_from(end.saturating_sub(start).max(0)).unwrap_or(usize::MAX);
    let mut result = String::new();
    for (index, character) in value.chars().enumerate() {
        if index % 1024 == 0 {
            check_interrupted()?;
        }
        if index >= start_index && index - start_index < count {
            result.push(character);
        } else if index >= start_index.saturating_add(count) {
            break;
        }
    }
    Ok(BuiltinResult::Value(string_term(result)))
}

fn length(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.length", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut length = 0_usize;
    for _ in value.chars() {
        if length.is_multiple_of(1024) {
            check_interrupted()?;
        }
        length += 1;
    }
    Ok(BuiltinResult::Value(int_term(BigInt::from(length))))
}

fn find(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.find", arguments, 3)?;
    let Some((haystack, needle)) = read_string(&arguments[0]).zip(read_string(&arguments[1]))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(start) = read_int(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let start = saturating_i64(&start);
    let haystack = haystack.chars().collect::<Vec<_>>();
    let needle = needle.chars().collect::<Vec<_>>();
    let start = usize::try_from(start.max(0)).unwrap_or(usize::MAX);
    let found = if needle.is_empty() {
        (start <= haystack.len()).then_some(start)
    } else {
        let mut found = None;
        if let Some(tail) = haystack.get(start..) {
            for (offset, window) in tail.windows(needle.len()).enumerate() {
                if offset % 1024 == 0 {
                    check_interrupted()?;
                }
                if window == needle {
                    found = Some(start + offset);
                    break;
                }
            }
        }
        found
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
    let Some(base) = read_int(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let base = match read_base(&base) {
        Ok(base) => base,
        Err(reason) => return Ok(BuiltinResult::Unsupported(reason)),
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
    let Some(base) = read_int(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let base = match read_base(&base) {
        Ok(base) => base,
        Err(reason) => return Ok(BuiltinResult::Unsupported(reason)),
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
    if (0xd800..=0xdfff).contains(&value) {
        return Ok(BuiltinResult::Value(string_term('\u{fffd}'.to_string())));
    }
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

fn string_to_token(
    arguments: &[Term],
    result_sort: Option<&Sort>,
) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("STRING.string2token", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(result_sort) = result_sort else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(Term::domain_value(
        result_sort.clone(),
        value,
    )))
}

fn read_base(base: &BigInt) -> Result<u32, UnsupportedHookReason> {
    base.to_u32()
        .filter(|base| (2..=36).contains(base))
        .ok_or_else(|| UnsupportedHookReason::ArgumentOutOfRange {
            detail: format!("base {base} is outside 2..36"),
        })
}

fn saturating_i64(value: &BigInt) -> i64 {
    value.to_i64().unwrap_or_else(|| {
        if value.sign() == Sign::Minus {
            i64::MIN
        } else {
            i64::MAX
        }
    })
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
        super::evaluate(hook, &arguments, None).unwrap()
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

    #[test]
    fn substr_follows_kore_take_and_drop() {
        for (start, end, expected) in [
            (-2, 3, "hello"),
            (1, 10, "ello"),
            (3, 1, ""),
            (-3, -1, "he"),
            (0, 0, ""),
        ] {
            assert_eq!(
                evaluate(
                    "STRING.substr",
                    vec![
                        string_term("hello"),
                        int_term(start.into()),
                        int_term(end.into())
                    ],
                ),
                BuiltinResult::Value(string_term(expected)),
                "substrString(hello, {start}, {end})"
            );
        }

        let beyond_i64: BigInt = BigInt::from(1_u8) << 100;
        assert_eq!(
            evaluate(
                "STRING.substr",
                vec![
                    string_term("hello"),
                    int_term(-&beyond_i64),
                    int_term(beyond_i64.clone()),
                ],
            ),
            BuiltinResult::Value(string_term("hello"))
        );
        assert_eq!(
            evaluate(
                "STRING.substr",
                vec![
                    string_term("hello"),
                    int_term(beyond_i64.clone()),
                    int_term(beyond_i64),
                ],
            ),
            BuiltinResult::Value(string_term(""))
        );
    }

    #[test]
    fn chr_replaces_surrogates_and_rejects_out_of_range() {
        assert_eq!(
            evaluate("STRING.chr", vec![int_term(55296.into())]),
            BuiltinResult::Value(string_term("\u{fffd}"))
        );
        assert_eq!(
            evaluate("STRING.chr", vec![int_term((-1).into())]),
            BuiltinResult::Bottom
        );
        assert_eq!(
            evaluate("STRING.chr", vec![int_term(0x110000.into())]),
            BuiltinResult::Bottom
        );
        assert_eq!(
            evaluate("STRING.chr", vec![int_term(0x1f980.into())]),
            BuiltinResult::Value(string_term("🦀"))
        );
    }

    #[test]
    fn find_keeps_domains_md_indices() {
        for (needle, start, expected) in [("l", 1, 2), ("l", 3, 3), ("", 5, 5), ("", 6, -1)] {
            assert_eq!(
                evaluate(
                    "STRING.find",
                    vec![
                        string_term("hello"),
                        string_term(needle),
                        int_term(start.into()),
                    ],
                ),
                BuiltinResult::Value(int_term(expected.into())),
                "findString(hello, {needle:?}, {start})"
            );
        }

        let beyond_i64: BigInt = BigInt::from(1_u8) << 100;
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![
                    string_term("hello"),
                    string_term("h"),
                    int_term(-&beyond_i64),
                ],
            ),
            BuiltinResult::Value(int_term(BigInt::from(0)))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![string_term("hello"), string_term("h"), int_term(beyond_i64),],
            ),
            BuiltinResult::Value(int_term(BigInt::from(-1)))
        );
    }

    #[test]
    fn bases_outside_two_through_thirty_six_are_unsupported() {
        for (hook, value) in [
            ("STRING.string2base", string_term("ff")),
            ("STRING.base2string", int_term(255.into())),
        ] {
            for base in [1, 37] {
                assert_eq!(
                    evaluate(hook, vec![value.clone(), int_term(base.into())]),
                    BuiltinResult::Unsupported(UnsupportedHookReason::ArgumentOutOfRange {
                        detail: format!("base {base} is outside 2..36"),
                    }),
                    "{hook} base {base}"
                );
            }
        }
    }
}
