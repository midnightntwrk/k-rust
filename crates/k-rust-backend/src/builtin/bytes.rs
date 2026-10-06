//! Deterministic `BYTES` hooks implemented by Kore's fallback evaluator.

use num_bigint::{BigInt, Sign};
use num_traits::{ToPrimitive, Zero};

use k_rust_kore::names::BuiltinSort;

use super::{
    BuiltinResult, HookResult, MAX_BYTES_RESULT_LEN, UnsupportedHookReason, describe_int,
    expect_arity, int_term, read_int, result_size_limit,
};
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
        "BYTES.padRight" => pad(arguments, false),
        "BYTES.padLeft" => pad(arguments, true),
        "BYTES.reverse" => reverse(arguments),
        "BYTES.length" => length(arguments),
        "BYTES.concat" => concatenate(arguments),
        "BYTES.int2bytes" => int_to_bytes(arguments),
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
/// the definition and the application is left unevaluated. A stored byte that starts no UTF-8
/// sequence is the code point of its own value.
fn string_to_bytes(arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity("BYTES.string2bytes", arguments, 1)?;
    let TermKind::DomainValue { sort, value } = arguments[0].kind() else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if !sort.is_builtin(BuiltinSort::String) {
        return Ok(BuiltinResult::NotApplicable);
    }
    let Some(bytes) = super::string::code_points(value.as_bytes())
        .map(|unit| u8::try_from(super::string::code_point_number(unit)).ok())
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
    let Some(encoding) = read_string(&arguments[0]) else {
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
    let Some((encoding, contents)) = read_string(&arguments[0]).zip(read_string(&arguments[1]))
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

fn pad(arguments: &[Term], left: bool) -> HookResult<BuiltinResult> {
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
    // The length, an `Int` and a byte value: `result_size_limit` of their sizes, in bytes.
    let arguments = (bytes.len() as u64)
        .saturating_add(length.bits().div_ceil(8))
        .saturating_add(1);
    let length = match bounded_length(&length, arguments) {
        Ok(length) => length,
        Err(reason) => return Ok(BuiltinResult::Unsupported(reason)),
    };
    let additional = length.saturating_sub(bytes.len());
    if left && additional != 0 {
        let mut padded = vec![value; additional];
        padded.extend(bytes);
        bytes = padded;
    } else {
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
/// not given by the definition and the application is left unevaluated.
fn int_to_bytes(arguments: &[Term]) -> HookResult<BuiltinResult> {
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
    // The length and the value, two `Int`s: `result_size_limit` of their sizes, in bytes.
    let arguments = length
        .bits()
        .div_ceil(8)
        .saturating_add(value.bits().div_ceil(8));
    let length = match bounded_length(&length, arguments) {
        Ok(length) => length,
        Err(reason) => return Ok(BuiltinResult::Unsupported(reason)),
    };
    // The low `length` bytes of the two's complement of `value`, least significant first: its
    // shortest two's-complement bytes, truncated or extended with its sign.
    let mut bytes = value.to_signed_bytes_le();
    let sign = if value.sign() == Sign::Minus { 0xff } else { 0 };
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

fn read_string(term: &Term) -> Option<&str> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    sort.is_builtin(BuiltinSort::String)
        .then(|| value.as_utf8().ok())
        .flatten()
}

/// A concrete `Int` argument as a position: `Some(None)` when it is negative or beyond every
/// position a `Bytes` value has, `None` when the argument is not a concrete `Int`, whose value
/// the hook cannot decide on.
fn read_index(term: &Term) -> Option<Option<usize>> {
    read_int(term).map(|value| value.to_usize())
}

/// A nonnegative `length` as the length of a result built from arguments of total size
/// `arguments` bytes, or `ResultTooLarge` above their `result_size_limit`
/// ([`MAX_BYTES_RESULT_LEN`]): the value exists, and the backend does not build it.
fn bounded_length(length: &BigInt, arguments: u64) -> Result<usize, UnsupportedHookReason> {
    debug_assert!(
        length.sign() != Sign::Minus,
        "callers reject a negative length"
    );
    let limit = result_size_limit(MAX_BYTES_RESULT_LEN, arguments);
    length
        .to_u64()
        .filter(|length| *length <= limit)
        .and_then(|length| usize::try_from(length).ok())
        .ok_or_else(|| UnsupportedHookReason::ResultTooLarge {
            detail: format!(
                "a Bytes result of length {} needs more than {limit} bytes",
                describe_int(length)
            ),
        })
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
    Term::domain_value(Sort::builtin(BuiltinSort::Bytes), bytes.to_vec())
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

    #[test]
    fn allocation_lengths_above_usize_are_unsupported() {
        let large_length = BigInt::from(1_u8) << usize::BITS;
        let length = int_term(large_length.clone());
        let expected = BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge {
            detail: format!(
                "a Bytes result of length a {}-bit integer needs more than {MAX_BYTES_RESULT_LEN} bytes",
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

    /// A length the arguments' values set is computed up to `result_size_limit` of their sizes,
    /// with [`MAX_BYTES_RESULT_LEN`] as the floor, and refused beyond it before anything is
    /// allocated: a length beyond the machine's memory aborted the process. Below the floor a
    /// length is built however long: 2^28 bytes (a padding built in under a second) and the floor
    /// itself, the largest memory a 32-bit address space holds (decided without allocating here).
    #[test]
    fn bytes_lengths_are_bounded_before_allocating() {
        let little = constructor("LbllittleEndianBytes", "SortEndianness");
        let refused = |result: HookResult<BuiltinResult>| {
            matches!(
                result,
                Ok(BuiltinResult::Unsupported(
                    UnsupportedHookReason::ResultTooLarge { .. }
                ))
            )
        };
        let floor = BigInt::from(MAX_BYTES_RESULT_LEN);
        for length in [&floor + 1u8, BigInt::from(1_u64 << 40)] {
            let length = int_term(length);
            for left in [false, true] {
                assert!(
                    refused(pad(&[bytes_term(b"abc"), length.clone(), integer(1)], left)),
                    "pad (left: {left}) to {length:?}"
                );
            }
            assert!(
                refused(int_to_bytes(&[length.clone(), integer(1), little.clone()])),
                "Int2Bytes({length:?}, 1, LE)"
            );
        }
        assert_eq!(
            pad(&[bytes_term(b"abc"), integer(5), integer(1)], true),
            Ok(BuiltinResult::Value(bytes_term(b"\x01\x01abc")))
        );
        for length in [1_u64 << 28, MAX_BYTES_RESULT_LEN] {
            assert_eq!(
                bounded_length(&BigInt::from(length), 3),
                Ok(usize::try_from(length).unwrap()),
                "a Bytes result of length {length}"
            );
        }
        // Relative to the arguments: twice their size, here the floor plus 4 bytes (a value of the
        // floor's length and a small length and byte), whatever the floor.
        let arguments = MAX_BYTES_RESULT_LEN + 4;
        assert_eq!(
            bounded_length(&BigInt::from(2 * arguments), arguments),
            Ok(usize::try_from(2 * arguments).unwrap())
        );
        assert!(bounded_length(&BigInt::from(2 * arguments + 1), arguments).is_err());
        assert_eq!(
            bounded_length(&floor, 3),
            Ok(usize::try_from(MAX_BYTES_RESULT_LEN).unwrap())
        );
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
        // A stored byte outside UTF-8 is the code point of its value.
        assert_eq!(
            string_to_bytes(&[Term::domain_value(
                Sort::builtin(BuiltinSort::String),
                vec![b'a', 0xe9, 0xff]
            )]),
            Ok(BuiltinResult::Value(bytes_term(&[b'a', 0xe9, 0xff])))
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
