//! Deterministic `STRING` hooks implemented by Kore's fallback evaluator.

use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

use k_rust_kore::kore::ast::KoreString;
use k_rust_kore::names::BuiltinSort;

use super::{
    BuiltinResult, HookResult, UnsupportedHookReason, bool_term, expect_arity, int_term, read_int,
};
use crate::term::{Sort, Term, TermKind};

pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    result_sort: Option<&Sort>,
) -> HookResult<BuiltinResult> {
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
        "STRING.find" => find(arguments, false),
        "STRING.rfind" => find(arguments, true),
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
    comparison: impl FnOnce(&[u8], &[u8]) -> bool,
) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 2)?;
    let Some((left, right)) =
        read_string_bytes(&arguments[0]).zip(read_string_bytes(&arguments[1]))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(bool_term(comparison(left, right))))
}

fn concatenate(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.concat", arguments, 2)?;
    let Some((left, right)) =
        read_string_bytes(&arguments[0]).zip(read_string_bytes(&arguments[1]))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut result = Vec::with_capacity(left.len().saturating_add(right.len()));
    result.extend_from_slice(left);
    result.extend_from_slice(right);
    Ok(BuiltinResult::Value(string_term(result)))
}

/// `substrString(S, START, END)` is the code points of S in `[START..END)` when
/// `0 <= START <= END <= lengthString(S)`. `domains.md` declares it `total` but says it is "only
/// defined on valid indices", so outside them it has a value the definition does not give: the
/// application is left unevaluated (`Unspecified`). Valid indices include `START == END`, which
/// the `domains.md` equations of `replaceFirst`, `findChar` and `countAllOccurrences` use.
fn substring(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.substr", arguments, 3)?;
    let Some(value) = read_string_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((start, end)) = read_int(&arguments[1]).zip(read_int(&arguments[2])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut starts = code_point_units(value).collect::<Vec<_>>();
    let units = starts.len();
    starts.push(value.len());
    if start.sign() == Sign::Minus || start > end || end > BigInt::from(units) {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::Unspecified {
                detail: format!(
                    "substrString from {start} to {end} on a string of length {units}, outside the valid indices 0 <= start <= end <= length"
                ),
            },
        ));
    }
    let (start, end) = (
        start
            .to_usize()
            .expect("a valid start is at most the length"),
        end.to_usize().expect("a valid end is at most the length"),
    );
    Ok(BuiltinResult::Value(string_term(
        value[starts[start]..starts[end]].to_vec(),
    )))
}

fn length(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.length", arguments, 1)?;
    let Some(value) = read_string_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        code_point_units(value).count(),
    ))))
}

/// `findString(S, N, I)` is the first occurrence of N in S starting at or after code point I,
/// and `rfindString(S, N, I)` the last starting at or before it, -1 when there is none; both are
/// defined for every integer I (`domains.md`: "starting at a certain index"). A negative I
/// searches `find` from 0 and leaves `rfind` nothing; an I past the end leaves `find` nothing
/// and searches `rfind` from the end.
fn find(arguments: &[Term], reverse: bool) -> HookResult<BuiltinResult> {
    let hook = if reverse {
        "STRING.rfind"
    } else {
        "STRING.find"
    };
    expect_arity(hook, arguments, 3)?;
    let Some((haystack, needle)) =
        read_string_bytes(&arguments[0]).zip(read_string_bytes(&arguments[1]))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(start) = read_int(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if reverse && start.sign() == Sign::Minus {
        return Ok(BuiltinResult::Value(int_term(BigInt::from(-1))));
    }
    let start = saturating_i64(&start);
    let start = usize::try_from(start.max(0)).unwrap_or(usize::MAX);
    // `starts[unit]` is the byte offset at which code point `unit` starts, and `boundary[offset]`
    // holds when a unit of the haystack starts at `offset`; the end of the haystack is both. A
    // match must start and end on a boundary, so it covers whole units of the haystack, and
    // those units are exactly the units of the needle: the unit decomposition from a boundary
    // depends only on the bytes that follow it.
    let mut starts = code_point_units(haystack).collect::<Vec<_>>();
    let units = starts.len();
    starts.push(haystack.len());
    let mut boundary = vec![false; haystack.len() + 1];
    for offset in &starts {
        boundary[*offset] = true;
    }
    let occurs_at = |unit: usize| {
        let offset = starts[unit];
        haystack[offset..].starts_with(needle) && boundary[offset + needle.len()]
    };
    let candidates: Box<dyn Iterator<Item = usize>> = if reverse {
        Box::new((0..=start.min(units)).rev())
    } else {
        Box::new(start.min(units + 1)..=units)
    };
    let mut found = None;
    for (step, unit) in candidates.enumerate() {
        if step % 1024 == 0 {
            crate::stop::check()?;
        }
        if occurs_at(unit) {
            found = Some(unit);
            break;
        }
    }
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        found
            .and_then(|index| i64::try_from(index).ok())
            .unwrap_or(-1),
    ))))
}

/// Byte offsets at which the code points of a stored `String` value start.
///
/// `String` is a sequence of code points; `length`, `substr` and `find` count and index them.
/// A stored value is a byte sequence: a valid UTF-8 sequence is one code point, and a byte that
/// does not begin a valid UTF-8 sequence (a raw `\xNN` escape or a byte read from a file) is
/// one code point on its own.
fn code_point_units(value: &[u8]) -> impl Iterator<Item = usize> + '_ {
    let mut offset = 0;
    std::iter::from_fn(move || {
        let rest = value.get(offset..).filter(|rest| !rest.is_empty())?;
        let start = offset;
        offset += code_point_unit_length(rest);
        Some(start)
    })
}

fn code_point_unit_length(bytes: &[u8]) -> usize {
    let length = match bytes[0] {
        0x00..=0x7f => return 1,
        0xc2..=0xdf => 2,
        0xe0..=0xef => 3,
        0xf0..=0xf4 => 4,
        _ => return 1,
    };
    match bytes.get(..length) {
        Some(sequence) if std::str::from_utf8(sequence).is_ok() => length,
        _ => 1,
    }
}

fn string_to_base(arguments: &[Term]) -> HookResult<BuiltinResult> {
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
    Ok(parse_integer(value, base)
        .map(int_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

/// An optional sign followed by one or more digits of `radix`, in either case. The integer
/// parser alone would also skip `_` separators, which are not digits.
fn parse_integer(value: &str, radix: u32) -> Option<BigInt> {
    let digits = value.strip_prefix(['+', '-']).unwrap_or(value);
    let well_formed =
        !digits.is_empty() && digits.chars().all(|character| character.is_digit(radix));
    well_formed
        .then(|| BigInt::parse_bytes(value.as_bytes(), radix))
        .flatten()
}

fn base_to_string(arguments: &[Term]) -> HookResult<BuiltinResult> {
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

fn string_to_int(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.string2int", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(parse_integer(value, 10)
        .map(int_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

fn int_to_string(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.int2string", arguments, 1)?;
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(value.to_string())))
}

/// `chrChar(N)` is the string of the one code point N. A String value holds no surrogate code
/// point (KORE string literals cannot write one) and no number outside the code points, so
/// `chrChar` of one has no value: it is undefined (the hook is partial).
fn chr(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.chr", arguments, 1)?;
    // A symbolic code point may be valid on some instances and invalid on others.
    let Some(value) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(value) = value.to_u32() else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(char::from_u32(value)
        .map(|value| string_term(value.to_string()))
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

/// `ordChar(S)` is the number of the one code point of S, undefined for any other length. A
/// stored byte that starts no UTF-8 sequence is one code point (`code_point_units`): the one a
/// `\xNN` escape writes, which both K's string syntax and the KORE language specification make
/// U+00NN, so its number is the byte's value.
fn ord(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.ord", arguments, 1)?;
    let Some(value) = read_string_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut units = code_point_units(value);
    let (Some(start), None) = (units.next(), units.next()) else {
        return Ok(BuiltinResult::Bottom);
    };
    debug_assert_eq!(start, 0);
    Ok(BuiltinResult::Value(int_term(BigInt::from(
        code_point_number(value),
    ))))
}

/// The number of the code point that the bytes of one unit (`code_point_units`) store.
pub(super) fn code_point_number(unit: &[u8]) -> u32 {
    match std::str::from_utf8(unit) {
        Ok(character) => u32::from(
            character
                .chars()
                .next()
                .expect("a unit holds one code point"),
        ),
        Err(_) => u32::from(unit[0]),
    }
}

/// The stored bytes of each code point of a `String` value (see `code_point_units`).
pub(super) fn code_points(value: &[u8]) -> impl Iterator<Item = &[u8]> + '_ {
    let mut starts = code_point_units(value).peekable();
    std::iter::from_fn(move || {
        let start = starts.next()?;
        let end = starts.peek().copied().unwrap_or(value.len());
        Some(&value[start..end])
    })
}

fn token_to_string(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("STRING.token2string", arguments, 1)?;
    let TermKind::DomainValue { value, .. } = arguments[0].kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(Term::domain_value(
        Sort::builtin(BuiltinSort::String),
        value.clone(),
    )))
}

fn string_to_token(arguments: &[Term], result_sort: Option<&Sort>) -> HookResult<BuiltinResult> {
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
    std::str::from_utf8(read_string_bytes(term)?).ok()
}

// A stored String value is a byte sequence (see `code_point_units`). Hooks that model textual
// conversions call `read_string`; the other string operations call this helper.
fn read_string_bytes(term: &Term) -> Option<&[u8]> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    sort.is_builtin(BuiltinSort::String)
        .then(|| value.as_bytes())
}

fn string_term(value: impl Into<KoreString>) -> Term {
    Term::domain_value(Sort::builtin(BuiltinSort::String), value.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn evaluate(hook: &str, arguments: Vec<Term>) -> BuiltinResult {
        super::evaluate(hook, &arguments, None).unwrap()
    }

    #[test]
    fn evaluates_string_operations_by_code_point() {
        assert_eq!(
            evaluate("STRING.length", vec![string_term("a🦀é")]),
            BuiltinResult::Value(int_term(BigInt::from(3)))
        );
        assert_eq!(
            evaluate(
                "STRING.substr",
                vec![string_term("a🦀é"), int_term(1.into()), int_term(2.into())]
            ),
            BuiltinResult::Value(string_term("🦀"))
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
    fn a_character_is_one_code_point_long() {
        for code_point in [233, 0xd7ff, 0xe000, 0x1f980] {
            let BuiltinResult::Value(character) =
                evaluate("STRING.chr", vec![int_term(code_point.into())])
            else {
                panic!("chrChar({code_point}) is defined");
            };
            assert_eq!(
                evaluate("STRING.length", vec![character]),
                BuiltinResult::Value(int_term(BigInt::from(1))),
                "lengthString(chrChar({code_point}))"
            );
        }
    }

    #[test]
    fn find_matches_whole_code_points_only() {
        // The lead byte of "é" alone is an invalid sequence, one code point, which does not occur
        // in "é".
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![
                    string_term("é"),
                    string_term(vec![0xc3]),
                    int_term(0.into())
                ]
            ),
            BuiltinResult::Value(int_term(BigInt::from(-1)))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![
                    string_term(vec![0xc3, b'x', 0xc3]),
                    string_term(vec![0xc3]),
                    int_term(1.into())
                ]
            ),
            BuiltinResult::Value(int_term(BigInt::from(2)))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![string_term("aé"), string_term(""), int_term(2.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(2)))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![string_term("aé"), string_term(""), int_term(3.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(-1)))
        );
    }

    #[test]
    fn string_operations_preserve_arbitrary_bytes() {
        let raw = || string_term(vec![0xff, 0x80, 0x00, b'A']);
        assert_eq!(
            evaluate("STRING.length", vec![raw()]),
            BuiltinResult::Value(int_term(BigInt::from(4)))
        );
        assert_eq!(
            evaluate(
                "STRING.substr",
                vec![raw(), int_term(1.into()), int_term(3.into())]
            ),
            BuiltinResult::Value(string_term(vec![0x80, 0x00]))
        );
        assert_eq!(
            evaluate(
                "STRING.find",
                vec![raw(), string_term(vec![0x80, 0x00]), int_term(0.into())]
            ),
            BuiltinResult::Value(int_term(BigInt::from(1)))
        );
        assert_eq!(
            evaluate(
                "STRING.concat",
                vec![string_term(vec![0xff]), string_term(vec![0x80, 0x00])]
            ),
            BuiltinResult::Value(string_term(vec![0xff, 0x80, 0x00]))
        );
        assert_eq!(
            evaluate("STRING.eq", vec![raw(), raw()]),
            BuiltinResult::Value(bool_term(true))
        );
        assert_eq!(
            evaluate(
                "STRING.lt",
                vec![string_term(vec![0x80]), string_term(vec![0xff])]
            ),
            BuiltinResult::Value(bool_term(true))
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

    /// `substrString` has its value on `0 <= start <= end <= length`, including empty ranges, and
    /// a value the definition leaves open elsewhere, so it is left unevaluated there.
    #[test]
    fn substr_is_unspecified_outside_valid_indices() {
        for (start, end, expected) in [(0, 0, ""), (5, 5, ""), (1, 3, "el"), (0, 5, "hello")] {
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
        for (start, end) in [
            (BigInt::from(-2), BigInt::from(3)),
            (BigInt::from(1), BigInt::from(10)),
            (BigInt::from(3), BigInt::from(1)),
            (BigInt::from(-3), BigInt::from(-1)),
            (BigInt::from(6), BigInt::from(6)),
            (-&beyond_i64, beyond_i64.clone()),
            (beyond_i64.clone(), beyond_i64.clone()),
        ] {
            assert!(
                matches!(
                    evaluate(
                        "STRING.substr",
                        vec![
                            string_term("hello"),
                            int_term(start.clone()),
                            int_term(end.clone())
                        ],
                    ),
                    BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })
                ),
                "substrString(hello, {start}, {end})"
            );
        }
    }

    /// No String holds a surrogate code point or a number outside the code points as a
    /// character, so `chrChar` of one is undefined; `ordChar(chrChar(N)) == N` wherever it is
    /// defined.
    #[test]
    fn chr_of_a_surrogate_or_a_non_code_point_is_undefined() {
        for code_point in [0xd800, 0xdbff, 0xdc00, 0xdfff] {
            assert_eq!(
                evaluate("STRING.chr", vec![int_term(code_point.into())]),
                BuiltinResult::Bottom,
                "chrChar({code_point})"
            );
        }
        for code_point in [0, 0xd7ff, 0xe000, 0x10ffff] {
            let BuiltinResult::Value(character) =
                evaluate("STRING.chr", vec![int_term(code_point.into())])
            else {
                panic!("chrChar({code_point}) is defined");
            };
            assert_eq!(
                evaluate("STRING.ord", vec![character]),
                BuiltinResult::Value(int_term(code_point.into())),
                "ordChar(chrChar({code_point}))"
            );
        }
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

    /// A stored byte that starts no UTF-8 sequence is the code point of the same number, the one
    /// a `\xNN` escape writes; a string of more or fewer than one code point has no `ordChar`.
    #[test]
    fn ord_of_a_raw_byte_is_its_value() {
        for (bytes, expected) in [(vec![0xe9], 233), (vec![0x80], 128), (vec![0xff], 255)] {
            assert_eq!(
                evaluate("STRING.ord", vec![string_term(bytes.clone())]),
                BuiltinResult::Value(int_term(BigInt::from(expected))),
                "ordChar({bytes:x?})"
            );
        }
        assert_eq!(
            evaluate("STRING.ord", vec![string_term("é")]),
            BuiltinResult::Value(int_term(BigInt::from(233)))
        );
        for bytes in [vec![0xff, 0xfe], vec![0xff, b'a'], vec![]] {
            assert_eq!(
                evaluate("STRING.ord", vec![string_term(bytes.clone())]),
                BuiltinResult::Bottom,
                "ordChar({bytes:x?})"
            );
        }
    }

    /// A symbolic code point may be valid on some instances, so `chrChar` of it is not decided.
    #[test]
    fn chr_of_a_symbolic_code_point_is_undecided() {
        let code_point = Term::variable(crate::term::Variable::new(
            "C",
            Sort::builtin(BuiltinSort::Int),
        ));
        assert_eq!(
            evaluate("STRING.chr", vec![code_point]),
            BuiltinResult::NotApplicable
        );
    }

    /// `findString` is the first occurrence starting at or after its index, whatever the index:
    /// a negative one searches from 0, one past the end finds nothing.
    #[test]
    fn find_searches_forward_from_any_index() {
        for (needle, start, expected) in [
            ("l", 1, 2),
            ("l", 3, 3),
            ("", 5, 5),
            ("", 6, -1),
            ("l", -5, 2),
            ("", -1, 0),
        ] {
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

    /// `rfindString` is the last occurrence starting at or before its index, whatever the index:
    /// none for a negative one, the last in the string for one past the end.
    #[test]
    fn rfind_searches_back_from_any_index() {
        let beyond_i64: BigInt = BigInt::from(1_u8) << 100;
        for (haystack, needle, start, expected) in [
            ("hello", "l", BigInt::from(4), 3),
            ("hello", "l", BigInt::from(2), 2),
            ("hello", "l", BigInt::from(1), -1),
            ("hello", "l", BigInt::from(100), 3),
            ("hello", "l", beyond_i64.clone(), 3),
            ("hello", "", BigInt::from(3), 3),
            ("hello", "", beyond_i64.clone(), 5),
            ("hello", "h", BigInt::from(-1), -1),
            ("hello", "", -beyond_i64.clone(), -1),
            ("a🦀é🦀", "🦀", BigInt::from(2), 1),
            ("a🦀é🦀", "🦀", BigInt::from(3), 3),
            ("", "", BigInt::from(0), 0),
        ] {
            assert_eq!(
                evaluate(
                    "STRING.rfind",
                    vec![
                        string_term(haystack),
                        string_term(needle),
                        int_term(start.clone())
                    ],
                ),
                BuiltinResult::Value(int_term(expected.into())),
                "rfindString({haystack:?}, {needle:?}, {start})"
            );
        }
        // The lead byte of "é" alone is a unit of its own and does not occur inside "é".
        assert_eq!(
            evaluate(
                "STRING.rfind",
                vec![
                    string_term("é"),
                    string_term(vec![0xc3]),
                    int_term(1.into())
                ]
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

    /// `String2Int` reads an optional sign and decimal digits, and `String2Base` the digits of
    /// its base in either case; a `_` separator is neither, so such strings are undefined.
    #[test]
    fn integer_conversions_accept_only_signed_digits() {
        let to_int = |text: &str| evaluate("STRING.string2int", vec![string_term(text)]);
        let to_base = |text: &str, base: i64| {
            evaluate(
                "STRING.string2base",
                vec![string_term(text), int_term(base.into())],
            )
        };
        assert_eq!(to_int("+15"), BuiltinResult::Value(int_term(15.into())));
        assert_eq!(to_int("-007"), BuiltinResult::Value(int_term((-7).into())));
        assert_eq!(
            to_base("fF", 16),
            BuiltinResult::Value(int_term(255.into()))
        );
        for text in ["1_0", "1_", "_1", "-_1", "", "+", "-", "+-1", " 1", "1e3"] {
            assert_eq!(to_int(text), BuiltinResult::Bottom, "{text:?}");
        }
        assert_eq!(to_base("f_f", 16), BuiltinResult::Bottom);
        assert_eq!(to_base("12", 2), BuiltinResult::Bottom);
    }
}
