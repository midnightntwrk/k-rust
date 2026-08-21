//! Deterministic `BYTES` hooks implemented by Kore's fallback evaluator.

use num_bigint::{BigInt, Sign};
use num_traits::{ToPrimitive, Zero};

use super::{BuiltinError, BuiltinResult, check_interrupted, expect_arity, int_term, read_int};
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

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
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
        _ => Ok(BuiltinResult::NotApplicable),
    }
}

fn empty(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.empty", arguments, 0)?;
    Ok(BuiltinResult::Value(bytes_term(&[])))
}

fn bytes_to_string(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.bytes2string", arguments, 1)?;
    let Some(bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(string_term(decode_8_bit(&bytes))))
}

fn string_to_bytes(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.string2bytes", arguments, 1)?;
    let Some(value) = read_string(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(bytes) = encode_8_bit(value) else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn decode_bytes(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
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

fn encode_bytes(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
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

fn update(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.update", arguments, 3)?;
    let Some(mut bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(index) = read_index(&arguments[1]) else {
        return Ok(BuiltinResult::Bottom);
    };
    let Some(value) = read_wrapping_byte(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(slot) = bytes.get_mut(index) else {
        return Ok(BuiltinResult::Bottom);
    };
    *slot = value;
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn get(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.get", arguments, 2)?;
    let Some(bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(index) = read_index(&arguments[1]) else {
        return Ok(BuiltinResult::Bottom);
    };
    let Some(value) = bytes.get(index) else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(*value))))
}

fn substring(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.substr", arguments, 3)?;
    let Some(bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(start) = read_index(&arguments[1]) else {
        return Ok(BuiltinResult::Bottom);
    };
    let Some(end) = read_index(&arguments[2]) else {
        return Ok(BuiltinResult::Bottom);
    };
    let Some(slice) = bytes.get(start..end) else {
        return Ok(BuiltinResult::Bottom);
    };
    Ok(BuiltinResult::Value(bytes_term(slice)))
}

fn replace_at(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.replaceAt", arguments, 3)?;
    let Some(mut bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(index) = read_index(&arguments[1]) else {
        return Ok(BuiltinResult::Bottom);
    };
    let Some(replacement) = read_bytes(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if replacement.is_empty() {
        return Ok(BuiltinResult::Value(bytes_term(&bytes)));
    }
    let Some(end) = index.checked_add(replacement.len()) else {
        return Ok(BuiltinResult::Bottom);
    };
    let Some(destination) = bytes.get_mut(index..end) else {
        return Ok(BuiltinResult::Bottom);
    };
    destination.copy_from_slice(&replacement);
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn pad(arguments: &[Term], left: bool) -> Result<BuiltinResult, BuiltinError> {
    let hook = if left {
        "BYTES.padLeft"
    } else {
        "BYTES.padRight"
    };
    expect_arity(hook, arguments, 3)?;
    let Some(mut bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(length) = read_nonnegative_len(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(value) = read_wrapping_byte(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
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

fn reverse(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.reverse", arguments, 1)?;
    let Some(mut bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    bytes.reverse();
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn length(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.length", arguments, 1)?;
    let Some(bytes) = read_bytes(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(int_term(BigInt::from(bytes.len()))))
}

fn concatenate(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.concat", arguments, 2)?;
    let Some((mut left, right)) = read_bytes(&arguments[0]).zip(read_bytes(&arguments[1])) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    left.extend(right);
    Ok(BuiltinResult::Value(bytes_term(&left)))
}

fn int_to_bytes(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity("BYTES.int2bytes", arguments, 3)?;
    let Some(length) = read_nonnegative_len(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(value) = read_int(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(endianness) = read_endianness(&arguments[2]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut current = value.clone();
    let mut bytes = Vec::with_capacity(length);
    for index in 0..length {
        if index % 1024 == 0 {
            check_interrupted()?;
        }
        bytes.push((&current & BigInt::from(0xff_u16)).to_u8().unwrap());
        current >>= 8;
    }
    if matches!(endianness, Endianness::Big) {
        bytes.reverse();
    }
    Ok(BuiltinResult::Value(bytes_term(&bytes)))
}

fn bytes_to_int(arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
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
            check_interrupted()?;
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
    if sort != &Sort::simple("SortBytes") {
        return None;
    }
    value
        .chars()
        .map(|character| u8::try_from(character as u32).ok())
        .collect()
}

fn read_string(term: &Term) -> Option<&str> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    (sort == &Sort::simple("SortString")).then_some(value.as_ref())
}

fn read_index(term: &Term) -> Option<usize> {
    read_int(term).and_then(|value| value.to_usize())
}

fn read_nonnegative_len(term: &Term) -> Option<usize> {
    let value = read_int(term)?;
    if value.sign() == Sign::Minus {
        Some(0)
    } else {
        value.to_usize()
    }
}

fn read_wrapping_byte(term: &Term) -> Option<u8> {
    let value = read_int(term)?;
    (value & BigInt::from(0xff_u16)).to_u8()
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
    Term::domain_value(
        Sort::simple("SortBytes"),
        bytes
            .iter()
            .map(|byte| char::from(*byte))
            .collect::<String>(),
    )
}

fn string_term(value: impl Into<String>) -> Term {
    Term::domain_value(Sort::simple("SortString"), value.into())
}

fn encode_8_bit(value: &str) -> Option<Vec<u8>> {
    value
        .chars()
        .map(|character| u8::try_from(character as u32).ok())
        .collect()
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
    let chunks = bytes.chunks_exact(2);
    if !chunks.remainder().is_empty() {
        return None;
    }
    let units = chunks
        .map(|chunk| match endianness {
            Endianness::Little => u16::from_le_bytes([chunk[0], chunk[1]]),
            Endianness::Big => u16::from_be_bytes([chunk[0], chunk[1]]),
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
    let chunks = bytes.chunks_exact(4);
    if !chunks.remainder().is_empty() {
        return None;
    }
    chunks
        .map(|chunk| {
            let bytes = [chunk[0], chunk[1], chunk[2], chunk[3]];
            char::from_u32(match endianness {
                Endianness::Little => u32::from_le_bytes(bytes),
                Endianness::Big => u32::from_be_bytes(bytes),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::term::Symbol;

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
            update(&[bytes.clone(), integer(1), integer(256)]),
            Ok(BuiltinResult::Value(bytes_term(&[0x00, 0x00, 0xff])))
        );
        assert_eq!(
            substring(&[bytes.clone(), integer(1), integer(3)]),
            Ok(BuiltinResult::Value(bytes_term(&[0x7f, 0xff])))
        );
        assert_eq!(get(&[bytes, integer(3)]), Ok(BuiltinResult::Bottom));
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
        assert_eq!(
            bytes_to_int(&[bytes_term(&[0xff, 0xfe]), big.clone(), signed]),
            Ok(BuiltinResult::Value(integer(-2)))
        );
        assert_eq!(
            bytes_to_int(&[bytes_term(&[0xff, 0xfe]), big, unsigned]),
            Ok(BuiltinResult::Value(integer(65_534)))
        );
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
