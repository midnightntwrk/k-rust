//! Deterministic `BYTES` hooks: per-call operations on byte strings.

use num_bigint::{BigInt, Sign};
use num_traits::{ToPrimitive, Zero};

use k_rust_kore::names::BuiltinSort;

use super::{
    BYTES_RESULT_PEAK_FACTOR, BuiltinResult, HookResult, ResultCap, TARGET_BYTES_RESULT_LEN,
    UnsupportedHookReason, describe_int, expect_arity, int_term, read_int,
};
use crate::allowance::Allowance;
use crate::term::{Sort, Term, TermKind};

#[derive(Clone, Copy)]
enum Endianness {
    Little,
    Big,
}

#[derive(Clone, Copy)]
enum Signedness {
    Signed,
    Unsigned,
}

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    match hook {
        "BYTES.empty" => empty(arguments),
        "BYTES.bytes2string" => bytes_to_string(arguments),
        "BYTES.string2bytes" => string_to_bytes(arguments),
        "BYTES.decodeBytes" => decode_bytes(arguments),
        "BYTES.encodeBytes" => encode_bytes(arguments),
        "BYTES.update" => update(arguments),
        "BYTES.get" => get(arguments),
        "BYTES.substr" => substring(arguments),
        "BYTES.replaceAt" => replace_at(arguments),
        "BYTES.padRight" => pad(arguments, false, Allowance::of_process()),
        "BYTES.padLeft" => pad(arguments, true, Allowance::of_process()),
        "BYTES.reverse" => reverse(arguments),
        "BYTES.length" => length(arguments),
        "BYTES.concat" => concatenate(arguments),
        "BYTES.int2bytes" => int_to_bytes(arguments, Allowance::of_process()),
        "BYTES.bytes2int" => bytes_to_int(arguments),
        _ => Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        )),
    }
}

fn empty(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.empty", arguments, 0)?;
    Ok(BuiltinResult::Value(bytes_term(&[])))
}

fn bytes_to_string(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.bytes2string", arguments, 1)?;
    let Some(bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(decode_8_bit(&bytes))))
}

/// `String2Bytes` is the inverse of `Bytes2String`. `domains.md` names no encoding for the pair
/// (it names one only for `encodeBytes`/`decodeBytes`, which take one); this backend reads it as
/// mapping each byte to the code point of the same number, its chosen reading. Totality does
/// not decide between readings: under this one `String2Bytes` has no value above 255, under
/// UTF-8 decoding `Bytes2String` has none on an invalid sequence. What decides is the module's
/// statement that only the first 256 code points are supported: on exactly those strings this
/// reading makes both `total` conversions total and mutually inverse, while UTF-8 decoding
/// leaves `Bytes2String` without a value on invalid sequences whatever strings are supported.
/// The hook is `total`, so on a string holding a code point above 255 its value is not given by
/// the definition and the application is left unevaluated.
fn string_to_bytes(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.string2bytes", arguments, 1)?;
    let Some(value) = super::string::read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(bytes) = value
        .chars()
        .map(|character| u8::try_from(u32::from(character)).ok())
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::Unspecified {
                detail: "String2Bytes of a string holding a code point above 255".into(),
            },
        ));
    };
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn decode_bytes(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.decodeBytes", arguments, 2)?;
    let Some(encoding) = super::string::read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(bytes) = read_bytes(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let decoded = match encoding {
        "UTF-8" => std::str::from_utf8(&bytes).ok().map(str::to_owned),
        "UTF-16LE" => decode_utf16(&bytes, Endianness::Little),
        "UTF-16BE" => decode_utf16(&bytes, Endianness::Big),
        "UTF-32LE" => decode_utf32(&bytes, Endianness::Little),
        "UTF-32BE" => decode_utf32(&bytes, Endianness::Big),
        _ => return Ok(BuiltinResult::NotApplicable),
    };
    Ok(decoded
        .map(string_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

fn encode_bytes(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.encodeBytes", arguments, 2)?;
    let Some((encoding, contents)) =
        super::string::read_string(&arguments[0]).zip(super::string::read_string(&arguments[1]))
    else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let bytes = match encoding {
        "UTF-8" => contents.as_bytes().to_vec(),
        "UTF-16LE" => encode_utf16(contents, Endianness::Little),
        "UTF-16BE" => encode_utf16(contents, Endianness::Big),
        "UTF-32LE" => encode_utf32(contents, Endianness::Little),
        "UTF-32BE" => encode_utf32(contents, Endianness::Big),
        _ => return Ok(BuiltinResult::NotApplicable),
    };
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn update(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.update", arguments, 3)?;
    let Some(mut bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(index) = read_index(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(index) = index else {
        return Ok(BuiltinResult::Bottom);
    };
    let Some(value) = read_byte(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((slot, value)) = bytes.get_mut(index).zip(value) else {
        return Ok(BuiltinResult::Bottom);
    };
    *slot = value;
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn get(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.get", arguments, 2)?;
    let Some(bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(index) = read_index(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(value) = index.and_then(|index| bytes.get(index)) else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(*value))))
}

fn substring(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.substr", arguments, 3)?;
    let Some(bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((start, end)) = read_index(&arguments[1]).zip(read_index(&arguments[2])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(slice) = start
        .zip(end)
        .and_then(|(start, end)| bytes.get(start..end))
    else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(BuiltinResult::Value(bytes_term(slice)))
}

/// `replaceAtBytes(DEST, INDEX, SRC)` replaces the bytes of `DEST` in `[INDEX, INDEX + N)`, N the
/// length of `SRC`; it is `#False` when that range is not inside `DEST`, that is unless
/// `0 <= INDEX` and `INDEX + N <= lengthBytes(DEST)`, as for `substrBytes`. An empty `SRC` at an
/// index past the end is therefore undefined, and at the end it changes nothing.
fn replace_at(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.replaceAt", arguments, 3)?;
    let Some(mut bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(index) = read_index(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(index) = index else {
        return Ok(BuiltinResult::Bottom);
    };
    let Some(replacement) = read_bytes(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(end) = index.checked_add(replacement.len()) else {
        return Ok(BuiltinResult::Bottom);
    };
    let Some(destination) = bytes.get_mut(index..end) else {
        return Ok(BuiltinResult::Bottom);
    };
    destination.copy_from_slice(&replacement);
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

/// `padRightBytes` (`left` false) or `padLeftBytes` (`left` true) under the cap that `allowance`
/// sets ([`bytes_result_cap`]).
fn pad(arguments: &[Term], left: bool, allowance: &Allowance) -> HookResult<BuiltinResult> {
    let hook = if left {
        "BYTES.padLeft"
    } else {
        "BYTES.padRight"
    };
    expect_arity(hook, arguments, 3)?;
    let Some(mut bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((length, value)) = read_int(&arguments[1]).zip(read_byte(&arguments[2])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(value) = value.filter(|_| length.sign() != Sign::Minus) else {
        return Ok(BuiltinResult::Bottom);
    };
    let length = match bounded_length(&length, &bytes_result_cap(allowance)) {
        Ok(length) => length,
        Err(reason) => return Ok(BuiltinResult::Unsupported(reason)),
    };
    let additional = length.saturating_sub(bytes.len());
    if left && additional != 0 {
        let mut padded = vec![value; additional];
        padded.extend(bytes);
        bytes = padded;
    } else {
        // Exactly the result's length: `resize` alone may reserve up to twice it.
        bytes.reserve_exact(additional);
        bytes.resize(bytes.len() + additional, value);
    }
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn reverse(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.reverse", arguments, 1)?;
    let Some(mut bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    bytes.reverse();
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn length(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.length", arguments, 1)?;
    let Some(bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(bytes.len()))))
}

fn concatenate(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.concat", arguments, 2)?;
    let Some((mut left, right)) = read_bytes(&arguments[0]).zip(read_bytes(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    left.extend(right);
    Ok(BuiltinResult::Value(bytes_term(&left)))
}

/// `Int2Bytes(LENGTH, I, E)` is the `LENGTH`-byte two's complement of `I` in byte order `E`. No
/// `Bytes` has a negative length and the hook is `total`, so for a negative `LENGTH` its value is
/// not given by the definition and the application is left unevaluated. A `LENGTH` above the cap
/// that `allowance` sets ([`bytes_result_cap`]) is refused.
fn int_to_bytes(arguments: &[Term], allowance: &Allowance) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.int2bytes", arguments, 3)?;
    if let Some(length) = read_int(&arguments[0])
        && length.sign() == Sign::Minus
    {
        return Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::Unspecified {
                detail: format!(
                    "Int2Bytes with the negative length {}",
                    describe_int(&length)
                ),
            },
        ));
    }
    let Some((length, value)) = read_int(&arguments[0]).zip(read_int(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(endianness) = read_endianness(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let length = match bounded_length(&length, &bytes_result_cap(allowance)) {
        Ok(length) => length,
        Err(reason) => return Ok(BuiltinResult::Unsupported(reason)),
    };
    // The low `length` bytes of the two's complement of `value`, least significant first: its
    // shortest two's-complement bytes, truncated or extended with its sign.
    let sign = if value.sign() == Sign::Minus { 0xff } else { 0 };
    let mut bytes = value.to_signed_bytes_le();
    // The value is not needed past its bytes, and the result is exactly `length` bytes:
    // `resize` alone may reserve up to twice the length.
    drop(value);
    bytes.reserve_exact(length.saturating_sub(bytes.len()));
    bytes.resize(length, sign);
    if matches!(endianness, Endianness::Big) {
        bytes.reverse();
    }
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn bytes_to_int(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.bytes2int", arguments, 3)?;
    let Some(mut bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(endianness) = read_endianness(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(signedness) = read_signedness(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if matches!(endianness, Endianness::Big) {
        bytes.reverse();
    }
    let mut unsigned = BigInt::zero();
    for (index, byte) in bytes.iter().rev().enumerate() {
        if index % 1024 == 0 {
            crate::stop::check()?;
        }
        unsigned = (unsigned << 8) + BigInt::from(*byte);
    }
    if matches!(signedness, Signedness::Signed) && bytes.last().is_some_and(|byte| byte & 0x80 != 0)
    {
        unsigned -= BigInt::from(1_u8) << (bytes.len() * 8);
    }
    Ok(BuiltinResult::Value(int_term(unsigned)))
}

pub(super) fn read_bytes(term: &Term) -> Option<Vec<u8>> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    if !sort.is_builtin(BuiltinSort::Bytes) {
        return None;
    }
    Some(value.as_bytes().to_vec())
}

/// A concrete `Int` argument as a position: `Some(None)` when it is negative or beyond every
/// position a `Bytes` value has, `None` when the argument is not a concrete `Int`, whose value
/// the hook cannot decide on.
fn read_index(term: &Term) -> Option<Option<usize>> {
    read_int(term).map(|value| value.to_usize())
}

/// A nonnegative `length` as the length of a `Bytes` result, or `ResultTooLarge` above `cap`:
/// the value exists, and the backend does not build it.
fn bounded_length(length: &BigInt, cap: &ResultCap<'_>) -> Result<usize, UnsupportedHookReason> {
    debug_assert!(
        length.sign() != Sign::Minus,
        "callers reject a negative length"
    );
    let limit = cap.bytes();
    length
        .to_u64()
        .filter(|length| *length <= limit)
        .and_then(|length| usize::try_from(length).ok())
        .ok_or_else(|| UnsupportedHookReason::ResultTooLarge {
            detail: format!(
                "a Bytes result of length {} is longer than its cap of {limit} bytes ({}): {}",
                describe_int(length),
                super::describe_bytes(limit),
                cap.reason(),
            ),
        })
}

/// The cap on a `Bytes` result whose length an argument's value sets (`padRightBytes`,
/// `padLeftBytes`, `Int2Bytes`): [`BYTES_RESULT_PEAK_FACTOR`] bytes held per byte of result
/// within `allowance`, and at most [`TARGET_BYTES_RESULT_LEN`], which leaves room to render the
/// result on a 32-bit target.
fn bytes_result_cap(allowance: &Allowance) -> ResultCap<'_> {
    bytes_result_cap_on(allowance, TARGET_BYTES_RESULT_LEN)
}

/// [`bytes_result_cap`] on a target where a result may take at most `target` bytes
/// ([`super::target_bytes_result_len`]); the tests use it to simulate a 32-bit target.
fn bytes_result_cap_on(allowance: &Allowance, target: u64) -> ResultCap<'_> {
    ResultCap::new(
        allowance,
        BYTES_RESULT_PEAK_FACTOR,
        target,
        "a sixteenth of the largest allocation on this target, so that the result can be rendered",
    )
}

/// A concrete `Int` argument as a byte value: `Some(None)` when it is outside `[0..255]`, `None`
/// when the argument is not a concrete `Int`.
fn read_byte(term: &Term) -> Option<Option<u8>> {
    read_int(term).map(|value| value.to_u8())
}

fn read_endianness(term: &Term) -> Option<Endianness> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    if !arguments.is_empty() {
        return None;
    }
    match symbol.name.as_ref() {
        "LbllittleEndianBytes" => Some(Endianness::Little),
        "LblbigEndianBytes" => Some(Endianness::Big),
        _ => None,
    }
}

fn read_signedness(term: &Term) -> Option<Signedness> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    if !arguments.is_empty() {
        return None;
    }
    match symbol.name.as_ref() {
        "LblsignedBytes" => Some(Signedness::Signed),
        "LblunsignedBytes" => Some(Signedness::Unsigned),
        _ => None,
    }
}

pub(super) fn bytes_term(bytes: &[u8]) -> Term {
    // One copy, straight into the shared buffer the term holds.
    Term::domain_value(
        Sort::builtin(BuiltinSort::Bytes),
        std::sync::Arc::<[u8]>::from(bytes),
    )
}

fn string_term(value: impl Into<String>) -> Term {
    Term::domain_value(Sort::builtin(BuiltinSort::String), value.into())
}

fn decode_8_bit(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| char::from(*byte)).collect()
}

fn encode_utf16(value: &str, endianness: Endianness) -> Vec<u8> {
    value
        .encode_utf16()
        .flat_map(|unit| match endianness {
            Endianness::Little => unit.to_le_bytes(),
            Endianness::Big => unit.to_be_bytes(),
        })
        .collect()
}

fn decode_utf16(bytes: &[u8], endianness: Endianness) -> Option<String> {
    let (chunks, remainder) = bytes.as_chunks::<2>();
    if !remainder.is_empty() {
        return None;
    }
    let units = chunks
        .iter()
        .map(|chunk| match endianness {
            Endianness::Little => u16::from_le_bytes(*chunk),
            Endianness::Big => u16::from_be_bytes(*chunk),
        })
        .collect::<Vec<_>>();
    String::from_utf16(&units).ok()
}

fn encode_utf32(value: &str, endianness: Endianness) -> Vec<u8> {
    value
        .chars()
        .flat_map(|character| match endianness {
            Endianness::Little => (character as u32).to_le_bytes(),
            Endianness::Big => (character as u32).to_be_bytes(),
        })
        .collect()
}

fn decode_utf32(bytes: &[u8], endianness: Endianness) -> Option<String> {
    let (chunks, remainder) = bytes.as_chunks::<4>();
    if !remainder.is_empty() {
        return None;
    }
    chunks
        .iter()
        .map(|chunk| {
            char::from_u32(match endianness {
                Endianness::Little => u32::from_le_bytes(*chunk),
                Endianness::Big => u32::from_be_bytes(*chunk),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::term::{Symbol, Variable};

    fn constructor(name: &str, sort: &str) -> Term {
        Term::application(
            Arc::new(Symbol::constructor(name, Vec::new(), Sort::simple(sort))),
            Vec::new(),
            Vec::new(),
        )
    }

    fn integer(value: i64) -> Term {
        int_term(BigInt::from(value))
    }

    #[test]
    fn converts_text_in_every_pinned_unicode_encoding() {
        for encoding in ["UTF-8", "UTF-16LE", "UTF-16BE", "UTF-32LE", "UTF-32BE"] {
            let encoded = evaluate(
                "BYTES.encodeBytes",
                &[string_term(encoding), string_term("A🦀")],
            )
            .unwrap();
            let BuiltinResult::Value(encoded) = encoded else {
                panic!("encoding should evaluate")
            };
            assert_eq!(
                evaluate("BYTES.decodeBytes", &[string_term(encoding), encoded]),
                Ok(BuiltinResult::Value(string_term("A🦀")))
            );
        }
    }

    #[test]
    fn byte_operations_preserve_octets_and_bottom() {
        let bytes = bytes_term(&[0x00, 0x7f, 0xff]);

        assert_eq!(
            get(&[bytes.clone(), integer(2)]),
            Ok(BuiltinResult::Value(integer(255)))
        );
        assert_eq!(
            update(&[bytes.clone(), integer(1), integer(0x80)]),
            Ok(BuiltinResult::Value(bytes_term(&[0x00, 0x80, 0xff])))
        );
        assert_eq!(
            substring(&[bytes.clone(), integer(1), integer(3)]),
            Ok(BuiltinResult::Value(bytes_term(&[0x7f, 0xff])))
        );
        assert_eq!(get(&[bytes, integer(3)]), Ok(BuiltinResult::Bottom));
    }

    /// An index the hook cannot read may be valid on some instances and invalid on others, so
    /// the application is not decided; a concrete index outside the value is `\bottom`.
    #[test]
    fn symbolic_indices_leave_the_application_undecided() {
        let bytes = bytes_term(b"abc");
        let index = Term::variable(Variable::new("I", Sort::builtin(BuiltinSort::Int)));
        let cases = [
            ("BYTES.get", vec![bytes.clone(), index.clone()]),
            (
                "BYTES.update",
                vec![bytes.clone(), index.clone(), integer(0)],
            ),
            (
                "BYTES.substr",
                vec![bytes.clone(), index.clone(), integer(2)],
            ),
            (
                "BYTES.substr",
                vec![bytes.clone(), integer(0), index.clone()],
            ),
            (
                "BYTES.replaceAt",
                vec![bytes.clone(), index, bytes_term(b"x")],
            ),
        ];
        for (hook, arguments) in cases {
            assert_eq!(
                evaluate(hook, &arguments),
                Ok(BuiltinResult::NotApplicable),
                "{hook}"
            );
        }
        assert_eq!(
            evaluate("BYTES.get", &[bytes.clone(), integer(-1)]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            evaluate("BYTES.substr", &[bytes, integer(2), integer(1)]),
            Ok(BuiltinResult::Bottom)
        );
    }

    /// `#False` if `value` is not in `[0..255]` (update and padding) or if the padding length
    /// is negative.
    #[test]
    fn byte_values_outside_a_byte_and_negative_padding_lengths_are_bottom() {
        let bytes = bytes_term(b"ab");
        for value in [-1, 256] {
            assert_eq!(
                update(&[bytes.clone(), integer(0), integer(value)]),
                Ok(BuiltinResult::Bottom)
            );
            for left in [false, true] {
                assert_eq!(
                    pad(&[bytes.clone(), integer(4), integer(value)], left),
                    Ok(BuiltinResult::Bottom)
                );
            }
        }
        for left in [false, true] {
            assert_eq!(
                pad(&[bytes.clone(), integer(-1), integer(0)], left),
                Ok(BuiltinResult::Bottom)
            );
            assert_eq!(
                pad(&[bytes.clone(), integer(1), integer(0)], left),
                Ok(BuiltinResult::Value(bytes.clone()))
            );
        }
        assert_eq!(
            pad(&[bytes.clone(), integer(3), integer(255)], true),
            Ok(BuiltinResult::Value(bytes_term(b"\xffab")))
        );
    }

    #[test]
    fn replace_at_past_the_end_is_bottom() {
        assert_eq!(
            replace_at(&[bytes_term(b"abc"), integer(2), bytes_term(b"xyz")]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            replace_at(&[bytes_term(b"abc"), integer(1), bytes_term(b"")]),
            Ok(BuiltinResult::Value(bytes_term(b"abc")))
        );
        assert_eq!(
            replace_at(&[bytes_term(b"abc"), integer(3), bytes_term(b"x")]),
            Ok(BuiltinResult::Bottom)
        );
        // An empty replacement range is inside `abc` at 0 to 3, and not after it.
        assert_eq!(
            replace_at(&[bytes_term(b"abc"), integer(3), bytes_term(b"")]),
            Ok(BuiltinResult::Value(bytes_term(b"abc")))
        );
        for index in [4, 100] {
            assert_eq!(
                replace_at(&[bytes_term(b"abc"), integer(index), bytes_term(b"")]),
                Ok(BuiltinResult::Bottom),
                "replaceAtBytes(abc, {index}, .Bytes)"
            );
        }
    }

    /// The allowance the hooks run under in these tests, so that whether a result is refused does
    /// not depend on the host: 16 GiB, a cap of 8 GiB on a `Bytes` result.
    static ALLOWANCE: Allowance = Allowance::given(16 << 30);

    fn pad(arguments: &[Term], left: bool) -> HookResult<BuiltinResult> {
        super::pad(arguments, left, &ALLOWANCE)
    }

    fn int_to_bytes(arguments: &[Term]) -> HookResult<BuiltinResult> {
        super::int_to_bytes(arguments, &ALLOWANCE)
    }

    fn refused(result: HookResult<BuiltinResult>) -> bool {
        matches!(
            result,
            Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::ResultTooLarge { .. }
            ))
        )
    }

    /// The refusal names the cap, the allowance it is a share of, where that allowance comes from,
    /// and the factor.
    #[test]
    fn allocation_lengths_above_usize_are_unsupported() {
        let large_length = BigInt::from(1_u8) << usize::BITS;
        let length = int_term(large_length.clone());
        let expected = BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge {
            detail: format!(
                "a Bytes result of length a {}-bit integer is longer than its cap of 8589934592 \
                 bytes (8 GiB): half of the 16 GiB this process may use (given by the embedder), \
                 since one application holds 2 bytes per byte of its result",
                large_length.bits()
            ),
        });

        assert_eq!(
            pad(&[bytes_term(b"abc"), length.clone(), integer(0)], false),
            Ok(expected.clone())
        );
        assert_eq!(
            pad(&[bytes_term(b"abc"), length.clone(), integer(0)], true),
            Ok(expected.clone())
        );
        assert_eq!(
            int_to_bytes(&[
                length,
                integer(0),
                constructor("LbllittleEndianBytes", "SortEndianness"),
            ]),
            Ok(expected)
        );
    }

    /// A length an argument's value sets is computed exactly when the application fits the
    /// allowance, [`BYTES_RESULT_PEAK_FACTOR`] bytes per byte of result, and refused beyond it
    /// before anything is allocated, whatever the size of the arguments: a value already at the
    /// cap is not padded past it. Under an allowance of 1 MiB the cap is 512 KiB, which the hooks
    /// build; under the tests' 16 GiB, 8 GiB is admitted (decided without allocating here).
    #[test]
    fn bytes_lengths_are_capped_by_the_allowance() {
        let small = Allowance::given(1 << 20);
        let cap = 1_u64 << 19;
        let little = constructor("LbllittleEndianBytes", "SortEndianness");
        let at_cap = vec![7; usize::try_from(cap).unwrap()];
        for left in [false, true] {
            assert!(
                super::pad(
                    &[bytes_term(b""), int_term(cap.into()), integer(7)],
                    left,
                    &small
                ) == Ok(BuiltinResult::Value(bytes_term(&at_cap))),
                "pad (left: {left}) to the cap"
            );
            for length in [BigInt::from(cap + 1), BigInt::from(1_u64 << 40)] {
                assert!(
                    refused(super::pad(
                        &[bytes_term(b"abc"), int_term(length.clone()), integer(1)],
                        left,
                        &small
                    )),
                    "pad (left: {left}) to {length}"
                );
            }
            assert!(
                refused(super::pad(
                    &[bytes_term(&at_cap), int_term((cap + 1).into()), integer(1)],
                    left,
                    &small
                )),
                "pad (left: {left}) a value at the cap past it"
            );
        }
        assert!(
            super::int_to_bytes(&[int_term(cap.into()), integer(-1), little.clone()], &small)
                == Ok(BuiltinResult::Value(bytes_term(&vec![
                    0xff;
                    usize::try_from(cap)
                        .unwrap()
                ]))),
            "Int2Bytes to the cap"
        );
        assert!(refused(super::int_to_bytes(
            &[int_term((cap + 1).into()), integer(-1), little],
            &small
        )));
        assert_eq!(
            pad(&[bytes_term(b"abc"), integer(5), integer(1)], true),
            Ok(BuiltinResult::Value(bytes_term(b"\x01\x01abc")))
        );
        let cap = bytes_result_cap(&ALLOWANCE);
        assert_eq!(cap.bytes(), 8 << 30);
        assert_eq!(
            bounded_length(&BigInt::from(8_u64 << 30), &cap),
            Ok(8 << 30)
        );
        assert!(bounded_length(&(BigInt::from(8_u64 << 30) + 1), &cap).is_err());
    }

    /// On a 32-bit target, whose largest allocation is 2^31 - 1 bytes and whose whole memory is at
    /// most 4 GiB, a `Bytes` result is at most a sixteenth of that allocation, 128 MiB, whatever
    /// the allowance: half the address space would let a length past `isize::MAX` reach the
    /// allocator, which panics, and a longer value could not be rendered (see
    /// `bytes_results_on_a_32_bit_target_can_be_rendered`). The refusal says so. On a 64-bit
    /// target the allowance binds first.
    #[test]
    fn bytes_lengths_are_bounded_by_what_the_target_can_allocate() {
        let thirty_two = super::super::target_bytes_result_len(u64::from(i32::MAX.unsigned_abs()));
        let address_space = Allowance::given(1 << 32);
        let cap = bytes_result_cap_on(&address_space, thirty_two);
        assert_eq!(cap.bytes(), 1 << 27);
        assert_eq!(
            cap.reason(),
            "a sixteenth of the largest allocation on this target, so that the result can be \
             rendered"
        );
        assert_eq!(
            bytes_result_cap_on(&Allowance::given(1 << 20), thirty_two).bytes(),
            1 << 19
        );
        let sixty_four = super::super::target_bytes_result_len(i64::MAX.unsigned_abs());
        assert_eq!(bytes_result_cap_on(&ALLOWANCE, sixty_four).bytes(), 8 << 30);
        assert_eq!(
            bytes_result_cap_on(&Allowance::given(u64::MAX), sixty_four).bytes(),
            1 << 59
        );
    }

    /// A `Bytes` result admitted on a 32-bit target can be written out there: KORE text spends at
    /// most four bytes on a byte (`\xhh`) and KORE JSON at most six (`\u00hh`), so the JSON of
    /// the longest admitted value is one allocation below `isize::MAX`, and the about sixteen
    /// bytes per byte that a library response holds at its peak stay within half of the address
    /// space, whatever the allowance there (at most the 4 GiB address space).
    #[test]
    fn bytes_results_on_a_32_bit_target_can_be_rendered() {
        use k_rust_kore::kore::{
            ast::{KoreString, Pattern, Sort as KoreSort},
            json, string,
        };
        let sort = KoreSort::Application {
            name: "SortBytes".into(),
            arguments: Vec::new(),
        };
        let json_length = |value: Vec<u8>| {
            json::to_string(&Pattern::DomainValue {
                sort: sort.clone(),
                value: KoreString::from(value),
            })
            .unwrap()
            .len()
        };
        let empty = json_length(Vec::new());
        for byte in 0..=u8::MAX {
            assert!(string::quote(&KoreString::from(vec![byte])).len() <= 2 + 4);
            assert!(json_length(vec![byte]) <= empty + 6, "{byte:#04x}");
        }
        let largest = u64::from(i32::MAX.unsigned_abs());
        let target = super::super::target_bytes_result_len(largest);
        for allowance in [0, 3, 1 << 20, 1 << 30, 1 << 32] {
            let length = bytes_result_cap_on(&Allowance::given(allowance), target).bytes();
            assert!(6 * length + 2 <= largest, "{allowance}: {length}");
            assert!(16 * length <= largest + 1, "{allowance}: {length}");
        }
    }

    /// The most memory one application holds, per byte of its result, is
    /// [`BYTES_RESULT_PEAK_FACTOR`]: measured with the test allocator at two result lengths, the
    /// peak grows by exactly that many bytes per byte of result, for each hook, each side of
    /// padding and inputs from empty to nearly as long as the result. The difference between the
    /// two lengths leaves out the few bytes an application holds whatever its length.
    #[test]
    fn bytes_hooks_hold_twice_their_result() {
        use crate::peak_memory::peak_during;
        let (shorter, longer) = (1_u64 << 24, 1_u64 << 25);
        let growth = |name: &str, peak: &dyn Fn(u64) -> u64| {
            let growth = peak(longer) - peak(shorter);
            let lengths = longer - shorter;
            assert!(
                growth <= BYTES_RESULT_PEAK_FACTOR * lengths
                    && growth > (BYTES_RESULT_PEAK_FACTOR - 1) * lengths,
                "{name}: the peak grew by {growth} bytes over {lengths} bytes of result"
            );
        };
        let input = |length: u64| vec![7; usize::try_from(length).unwrap()];
        for left in [false, true] {
            for (shape, input_length) in [
                ("empty", &(|_| 0_u64) as &dyn Fn(u64) -> u64),
                ("half as long", &|length| length / 2),
                ("one byte shorter", &|length| length - 1),
            ] {
                growth(&format!("pad (left: {left}), input {shape}"), &|length| {
                    let arguments = [
                        bytes_term(&input(input_length(length))),
                        int_term(length.into()),
                        integer(1),
                    ];
                    let (result, peak) = peak_during(|| pad(&arguments, left));
                    assert!(matches!(result, Ok(BuiltinResult::Value(_))));
                    peak
                });
            }
        }
        for endianness in ["LbllittleEndianBytes", "LblbigEndianBytes"] {
            growth(&format!("Int2Bytes, {endianness}"), &|length| {
                let arguments = [
                    int_term(length.into()),
                    integer(-1),
                    constructor(endianness, "SortEndianness"),
                ];
                let (result, peak) = peak_during(|| int_to_bytes(&arguments));
                assert!(matches!(result, Ok(BuiltinResult::Value(_))));
                peak
            });
        }
    }

    #[test]
    fn integer_conversions_match_twos_complement_and_endianness() {
        let little = constructor("LbllittleEndianBytes", "SortEndianness");
        let big = constructor("LblbigEndianBytes", "SortEndianness");
        let signed = constructor("LblsignedBytes", "SortSignedness");
        let unsigned = constructor("LblunsignedBytes", "SortSignedness");

        assert_eq!(
            int_to_bytes(&[integer(2), integer(0x1234), little.clone()]),
            Ok(BuiltinResult::Value(bytes_term(&[0x34, 0x12])))
        );
        assert_eq!(
            int_to_bytes(&[integer(2), integer(-2), big.clone()]),
            Ok(BuiltinResult::Value(bytes_term(&[0xff, 0xfe])))
        );
        // Sign extension, truncation to the low bytes, and an empty result.
        assert_eq!(
            int_to_bytes(&[integer(4), integer(-2), little.clone()]),
            Ok(BuiltinResult::Value(bytes_term(&[0xfe, 0xff, 0xff, 0xff])))
        );
        assert_eq!(
            int_to_bytes(&[integer(3), integer(255), big.clone()]),
            Ok(BuiltinResult::Value(bytes_term(&[0, 0, 0xff])))
        );
        assert_eq!(
            int_to_bytes(&[integer(1), integer(0x1234), little.clone()]),
            Ok(BuiltinResult::Value(bytes_term(&[0x34])))
        );
        assert_eq!(
            int_to_bytes(&[integer(1), integer(-129), little.clone()]),
            Ok(BuiltinResult::Value(bytes_term(&[0x7f])))
        );
        assert_eq!(
            int_to_bytes(&[integer(0), integer(-1), big.clone()]),
            Ok(BuiltinResult::Value(bytes_term(&[])))
        );
        assert_eq!(
            bytes_to_int(&[bytes_term(&[0xff, 0xfe]), big.clone(), signed]),
            Ok(BuiltinResult::Value(integer(-2)))
        );
        assert_eq!(
            bytes_to_int(&[bytes_term(&[0xff, 0xfe]), big, unsigned]),
            Ok(BuiltinResult::Value(integer(65_534)))
        );
    }

    /// Under the byte-per-code-point reading of the pair (this backend's chosen reading; see
    /// `string_to_bytes`), every code point up to 255 is the byte of the same number, and a
    /// string with a code point above 255 has no byte sequence `Bytes2String` maps to it.
    #[test]
    fn string_to_bytes_above_255_is_unspecified() {
        assert_eq!(
            string_to_bytes(&[string_term("a\u{ff}")]),
            Ok(BuiltinResult::Value(bytes_term(&[b'a', 0xff])))
        );
        // Each code point up to 255 is the byte of its value, `é` (U+00E9) included.
        assert_eq!(
            string_to_bytes(&[string_term("aé\u{ff}")]),
            Ok(BuiltinResult::Value(bytes_term(&[b'a', 0xe9, 0xff])))
        );
        // A payload that is not UTF-8 is no `String` value.
        assert_eq!(
            string_to_bytes(&[Term::domain_value(
                Sort::builtin(BuiltinSort::String),
                vec![b'a', 0xe9, 0xff]
            )]),
            Ok(BuiltinResult::NotApplicable)
        );
        for text in ["\u{100}", "a🦀"] {
            assert!(
                matches!(
                    string_to_bytes(&[string_term(text)]),
                    Ok(BuiltinResult::Unsupported(
                        UnsupportedHookReason::Unspecified { .. }
                    ))
                ),
                "String2Bytes({text:?})"
            );
        }
    }

    /// No `Bytes` value has a negative length, so `Int2Bytes` with one has no value the
    /// definition gives; a zero length is the empty `Bytes`.
    #[test]
    fn int_to_bytes_with_a_negative_length_is_unspecified() {
        let little = constructor("LbllittleEndianBytes", "SortEndianness");
        assert_eq!(
            int_to_bytes(&[integer(0), integer(5), little.clone()]),
            Ok(BuiltinResult::Value(bytes_term(&[])))
        );
        for length in [-1, -8] {
            assert!(
                matches!(
                    int_to_bytes(&[integer(length), integer(5), little.clone()]),
                    Ok(BuiltinResult::Unsupported(
                        UnsupportedHookReason::Unspecified { .. }
                    ))
                ),
                "Int2Bytes({length}, 5, LE)"
            );
        }
    }

    #[test]
    fn rejects_invalid_unicode_sequences() {
        assert_eq!(
            decode_bytes(&[string_term("UTF-8"), bytes_term(&[0xff])]),
            Ok(BuiltinResult::Bottom)
        );
        assert_eq!(
            decode_bytes(&[string_term("UTF-16LE"), bytes_term(&[0x00])]),
            Ok(BuiltinResult::Bottom)
        );
    }
}
