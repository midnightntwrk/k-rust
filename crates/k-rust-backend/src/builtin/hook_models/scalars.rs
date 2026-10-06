//! `BYTES` against byte vectors and `STRING` against code-point sequences.
//!
//! A stored `String` is a byte sequence; its code points are its valid UTF-8 sequences, and a
//! byte that begins none is a code point of its own (`code_point_units` in `string.rs`). The
//! model splits a value with the standard library's `Utf8Chunks` instead, one unit per decoded
//! character and per byte of an invalid chunk.

use num_bigint::{BigInt, Sign};
use num_traits::{Signed, ToPrimitive, Zero};

use k_rust_kore::names::BuiltinSort;

use super::{Case, Draw, Env, Spec, Val, assert_reached, encode, run, tag};
use crate::term::{Sort, Term};

const CASES: u32 = 3000;

fn bytes_value(draw: &mut Draw<'_>, most: usize) -> Vec<u8> {
    (0..draw.below(most + 1))
        .map(|_| {
            let random = draw.byte();
            draw.pick(&[0x00, 0x01, 0x41, 0x7f, 0x80, 0xc3, 0xa9, 0xfe, 0xff, random])
        })
        .collect()
}

fn bytes(draw: &mut Draw<'_>, env: &mut Env, most: usize) -> Term {
    let value = bytes_value(draw, most);
    draw.scalar(
        encode(&Val::Bytes(value)),
        Sort::builtin(BuiltinSort::Bytes),
        env,
    )
}

/// Text pieces: ASCII, two-, three- and four-byte characters, and bytes that begin no valid
/// UTF-8 sequence (alone, or as a truncated one).
const PIECES: [&[u8]; 14] = [
    b"a",
    b"b",
    b"ab",
    b"0",
    b"-",
    "é".as_bytes(),
    "ÿ".as_bytes(),
    "€".as_bytes(),
    "🦀".as_bytes(),
    "\u{fffd}".as_bytes(),
    b"\x00",
    b"\xc3",
    b"\xff",
    b"\xe2\x82",
];

fn text_value(draw: &mut Draw<'_>, most: usize) -> Vec<u8> {
    (0..draw.below(most + 1))
        .flat_map(|_| draw.pick(&PIECES).to_vec())
        .collect()
}

fn string(draw: &mut Draw<'_>, env: &mut Env, value: Vec<u8>) -> Term {
    draw.scalar(
        encode(&Val::Str(value)),
        Sort::builtin(BuiltinSort::String),
        env,
    )
}

fn text(draw: &mut Draw<'_>, env: &mut Env, most: usize) -> Term {
    let value = text_value(draw, most);
    string(draw, env, value)
}

/// A numeral-like string: an optional sign and digits of several bases, sometimes with a
/// character no base accepts.
fn numeral(draw: &mut Draw<'_>) -> Vec<u8> {
    let mut value = Vec::new();
    if draw.chance(3) {
        value.push(draw.pick(b"-+"));
    }
    for _ in 0..draw.below(5) {
        value.push(draw.pick(b"0179afzAFZ -."));
    }
    if draw.chance(1) {
        value.extend(draw.pick(&PIECES));
    }
    value
}

fn small_int(draw: &mut Draw<'_>) -> BigInt {
    match draw.below(8) {
        0 => BigInt::from(draw.u64()) * BigInt::from(draw.u64()),
        1 => -BigInt::from(draw.u64()),
        2 => BigInt::from(draw.below(512)) - 256,
        _ => BigInt::from(draw.below(40)) - 8,
    }
}

// ---------------------------------------------------------------------------------------------
// BYTES

const BYTES_HOOKS: [&str; 16] = [
    "BYTES.empty",
    "BYTES.bytes2string",
    "BYTES.string2bytes",
    "BYTES.decodeBytes",
    "BYTES.encodeBytes",
    "BYTES.update",
    "BYTES.get",
    "BYTES.substr",
    "BYTES.replaceAt",
    "BYTES.padRight",
    "BYTES.padLeft",
    "BYTES.reverse",
    "BYTES.length",
    "BYTES.concat",
    "BYTES.int2bytes",
    "BYTES.bytes2int",
];

const ENCODINGS: [&str; 6] = [
    "UTF-8", "UTF-16LE", "UTF-16BE", "UTF-32LE", "UTF-32BE", "latin1",
];

fn byte_value_argument(draw: &mut Draw<'_>, env: &mut Env) -> Term {
    let value = draw.pick(&[0, 1, 127, 128, 255, 256, -1, 511]);
    draw.int(value, env)
}

fn endianness(draw: &mut Draw<'_>, env: &mut Env) -> Term {
    let name = draw.pick(&["LbllittleEndianBytes", "LblbigEndianBytes"]);
    draw.scalar(
        tag(name, "SortEndianness"),
        Sort::simple("SortEndianness"),
        env,
    )
}

fn bytes_case(draw: &mut Draw<'_>) -> Case {
    let hook = draw.pick(&BYTES_HOOKS);
    let mut env = Env::new();
    let env = &mut env;
    let arguments = match hook {
        "BYTES.empty" => vec![],
        "BYTES.bytes2string" | "BYTES.reverse" | "BYTES.length" => vec![bytes(draw, env, 6)],
        "BYTES.string2bytes" => vec![text(draw, env, 4)],
        "BYTES.decodeBytes" => {
            let encoding = draw.pick(&ENCODINGS);
            // Valid encodings of text half of the time, arbitrary bytes otherwise.
            let contents = if draw.chance(4) {
                let text = String::from_utf8_lossy(&text_value(draw, 3)).into_owned();
                encode_text(encoding, &text).unwrap_or_default()
            } else {
                bytes_value(draw, 8)
            };
            vec![
                string(draw, env, encoding.as_bytes().to_vec()),
                draw.scalar(
                    encode(&Val::Bytes(contents)),
                    Sort::builtin(BuiltinSort::Bytes),
                    env,
                ),
            ]
        }
        "BYTES.encodeBytes" => {
            let encoding = draw.pick(&ENCODINGS);
            vec![
                string(draw, env, encoding.as_bytes().to_vec()),
                text(draw, env, 3),
            ]
        }
        "BYTES.update" => {
            let target = bytes(draw, env, 4);
            let index = draw.index(4);
            vec![target, draw.int(index, env), byte_value_argument(draw, env)]
        }
        "BYTES.get" => {
            let target = bytes(draw, env, 4);
            let index = draw.index(4);
            vec![target, draw.int(index, env)]
        }
        "BYTES.substr" => {
            let target = bytes(draw, env, 4);
            let (start, end) = (draw.index(4), draw.index(4));
            vec![target, draw.int(start, env), draw.int(end, env)]
        }
        "BYTES.replaceAt" => {
            let target = bytes(draw, env, 5);
            let index = draw.index(5);
            vec![target, draw.int(index, env), bytes(draw, env, 3)]
        }
        "BYTES.padRight" | "BYTES.padLeft" => {
            let target = bytes(draw, env, 4);
            let length = draw.below(9) as i64 - 2;
            vec![
                target,
                draw.int(length, env),
                byte_value_argument(draw, env),
            ]
        }
        "BYTES.concat" => vec![bytes(draw, env, 4), bytes(draw, env, 4)],
        "BYTES.int2bytes" => {
            let length = draw.below(8) as i64 - 1;
            let value = small_int(draw);
            vec![
                draw.int(length, env),
                draw.int(value, env),
                endianness(draw, env),
            ]
        }
        "BYTES.bytes2int" => {
            let signedness = draw.pick(&["LblsignedBytes", "LblunsignedBytes"]);
            vec![
                bytes(draw, env, 6),
                endianness(draw, env),
                draw.scalar(
                    tag(signedness, "SortSignedness"),
                    Sort::simple("SortSignedness"),
                    env,
                ),
            ]
        }
        _ => unreachable!(),
    };
    Case {
        hook,
        arguments,
        env: env.clone(),
    }
}

fn encode_text(encoding: &str, text: &str) -> Option<Vec<u8>> {
    if !ENCODINGS[..5].contains(&encoding) {
        return None;
    }
    let mut bytes = Vec::new();
    for character in text.chars() {
        let mut units = [0_u16; 2];
        match encoding {
            "UTF-8" => bytes.extend(character.encode_utf8(&mut [0; 4]).as_bytes()),
            "UTF-16LE" => {
                for unit in character.encode_utf16(&mut units) {
                    bytes.extend(unit.to_le_bytes());
                }
            }
            "UTF-16BE" => {
                for unit in character.encode_utf16(&mut units) {
                    bytes.extend(unit.to_be_bytes());
                }
            }
            "UTF-32LE" => bytes.extend(u32::from(character).to_le_bytes()),
            "UTF-32BE" => bytes.extend(u32::from(character).to_be_bytes()),
            _ => return None,
        }
    }
    Some(bytes)
}

/// The text whose encoding is `bytes`, `Some(None)` when there is none, `None` for an encoding
/// the documentation does not list.
fn decode_text(encoding: &str, bytes: &[u8]) -> Option<Option<String>> {
    let units16 = |big: bool| {
        bytes
            .chunks(2)
            .map(|chunk| {
                let pair: [u8; 2] = chunk.try_into().ok()?;
                Some(if big {
                    u16::from_be_bytes(pair)
                } else {
                    u16::from_le_bytes(pair)
                })
            })
            .collect::<Option<Vec<_>>>()
            .and_then(|units| String::from_utf16(&units).ok())
    };
    let units32 = |big: bool| {
        bytes
            .chunks(4)
            .map(|chunk| {
                let quad: [u8; 4] = chunk.try_into().ok()?;
                char::from_u32(if big {
                    u32::from_be_bytes(quad)
                } else {
                    u32::from_le_bytes(quad)
                })
            })
            .collect::<Option<String>>()
    };
    Some(match encoding {
        "UTF-8" => String::from_utf8(bytes.to_vec()).ok(),
        "UTF-16LE" => units16(false),
        "UTF-16BE" => units16(true),
        "UTF-32LE" => units32(false),
        "UTF-32BE" => units32(true),
        _ => return None,
    })
}

/// The non-negative `value` as a `usize` no larger than `bound`, if it is one.
fn at_most(value: &BigInt, bound: usize) -> Option<usize> {
    value.to_usize().filter(|value| *value <= bound)
}

fn byte(value: &BigInt) -> Option<u8> {
    value.to_u8()
}

fn little_endian(tag: &str) -> bool {
    match tag {
        "LbllittleEndianBytes" => true,
        "LblbigEndianBytes" => false,
        _ => panic!("not an endianness: {tag}"),
    }
}

fn bytes_model(hook: &str, arguments: &[Val]) -> Spec {
    use Val::{Bytes, Int, Str, Tag};
    match (hook, arguments) {
        ("BYTES.empty", []) => Spec::value(Bytes(Vec::new())),
        // Each byte is the code point of the same number.
        ("BYTES.bytes2string", [Bytes(bytes)]) => Spec::value(Str(bytes
            .iter()
            .map(|byte| char::from(*byte))
            .collect::<String>()
            .into_bytes())),
        // The code point of each unit, a raw byte standing for U+00NN, as one byte.
        ("BYTES.string2bytes", [Str(text)]) => units(text)
            .into_iter()
            .map(|unit| match std::str::from_utf8(unit) {
                Ok(character) => u8::try_from(u32::from(character.chars().next().unwrap())).ok(),
                Err(_) => Some(unit[0]),
            })
            .collect::<Option<Vec<_>>>()
            .map_or_else(
                // `String2Bytes` is total, but no byte is a code point above 255, so the
                // documentation gives no value for such a string.
                Spec::unspecified,
                |bytes| Spec::value(Bytes(bytes)),
            ),
        ("BYTES.decodeBytes", [Str(encoding), Bytes(bytes)]) => {
            match decode_text(std::str::from_utf8(encoding).unwrap(), bytes) {
                Some(text) => Spec::partial(text.map(|text| Str(text.into_bytes()))),
                None => Spec::open(),
            }
        }
        ("BYTES.encodeBytes", [Str(encoding), Str(text)]) => {
            match (
                std::str::from_utf8(encoding).unwrap(),
                std::str::from_utf8(text),
            ) {
                (encoding, Ok(text)) => encode_text(encoding, text)
                    .map_or_else(Spec::open, |bytes| Spec::value(Bytes(bytes))),
                // A stored string with bytes outside UTF-8 has no Unicode encoding.
                (_, Err(_)) => Spec::open(),
            }
        }
        // `#False` (undefined) if `value` is not in [0..255] or `index` is not a valid index.
        ("BYTES.update", [Bytes(bytes), Int(index), Int(value)]) => Spec::partial(
            index
                .to_usize()
                .filter(|index| *index < bytes.len())
                .zip(byte(value))
                .map(|(index, value)| {
                    let mut bytes = bytes.clone();
                    bytes[index] = value;
                    Bytes(bytes)
                }),
        ),
        ("BYTES.get", [Bytes(bytes), Int(index)]) => Spec::partial(
            index
                .to_usize()
                .and_then(|index| bytes.get(index))
                .map(|byte| Val::int(*byte)),
        ),
        // `#Bottom` if `startIndex < 0`, `endIndex < startIndex` or `length < endIndex`.
        ("BYTES.substr", [Bytes(bytes), Int(start), Int(end)]) => Spec::partial(
            at_most(end, bytes.len())
                .zip(start.to_usize())
                .filter(|(end, start)| start <= end)
                .map(|(end, start)| Bytes(bytes[start..end].to_vec())),
        ),
        ("BYTES.replaceAt", [Bytes(bytes), Int(index), Bytes(source)]) => {
            match index
                .to_usize()
                .filter(|index| index + source.len() <= bytes.len())
            {
                Some(index) => {
                    let mut bytes = bytes.clone();
                    bytes[index..index + source.len()].copy_from_slice(source);
                    Spec::value(Bytes(bytes))
                }
                // `#False` unless the replaced range lies inside the value, an empty one too.
                None => Spec::bottom(),
            }
        }
        // `#False` if `value` is not in [0..255], or if the length is negative.
        ("BYTES.padRight" | "BYTES.padLeft", [Bytes(bytes), Int(length), Int(value)]) => {
            Spec::partial(length.to_usize().zip(byte(value)).map(|(length, value)| {
                let padding = vec![value; length.saturating_sub(bytes.len())];
                Bytes(if hook == "BYTES.padLeft" {
                    padding.iter().chain(bytes).copied().collect()
                } else {
                    bytes.iter().chain(&padding).copied().collect()
                })
            }))
        }
        ("BYTES.reverse", [Bytes(bytes)]) => {
            Spec::value(Bytes(bytes.iter().rev().copied().collect()))
        }
        ("BYTES.length", [Bytes(bytes)]) => Spec::value(Val::int(bytes.len())),
        ("BYTES.concat", [Bytes(left), Bytes(right)]) => {
            Spec::value(Bytes(left.iter().chain(right).copied().collect()))
        }
        // The value modulo 256^length (two's complement, truncated), in the byte order. No
        // Bytes has a negative length, and the hook is total: that value is unspecified.
        ("BYTES.int2bytes", [Int(length), Int(value), Tag(order)]) => match length.to_usize() {
            Some(length) => {
                let modulus = BigInt::from(1_u8) << (8 * length);
                let mut residue = ((value % &modulus) + &modulus) % &modulus;
                let mut bytes = Vec::with_capacity(length);
                for _ in 0..length {
                    bytes.push((&residue % 256_u32).to_u8().unwrap());
                    residue >>= 8;
                }
                if !little_endian(order) {
                    bytes.reverse();
                }
                Spec::value(Bytes(bytes))
            }
            None if length.is_negative() => Spec::unspecified(),
            None => Spec::open(),
        },
        ("BYTES.bytes2int", [Bytes(bytes), Tag(order), Tag(signedness)]) => {
            let mut most_significant_first = bytes.clone();
            if little_endian(order) {
                most_significant_first.reverse();
            }
            let unsigned = BigInt::from_bytes_be(Sign::Plus, &most_significant_first);
            let negative = signedness == "LblsignedBytes"
                && most_significant_first
                    .first()
                    .is_some_and(|byte| byte & 0x80 != 0);
            Spec::value(Int(if negative {
                unsigned - (BigInt::from(1_u8) << (8 * bytes.len()))
            } else {
                unsigned
            }))
        }
        _ => panic!("no BYTES model for {hook} on {arguments:?}"),
    }
}

#[test]
fn bytes_hooks_agree_with_a_byte_vector_model() {
    let tallies = run(CASES, &bytes_case, &bytes_model);
    assert_reached(&tallies, &BYTES_HOOKS, &[]);
}

// ---------------------------------------------------------------------------------------------
// STRING

const STRING_HOOKS: [&str; 18] = [
    "STRING.eq",
    "STRING.ne",
    "STRING.lt",
    "STRING.le",
    "STRING.gt",
    "STRING.ge",
    "STRING.concat",
    "STRING.substr",
    "STRING.length",
    "STRING.find",
    "STRING.rfind",
    "STRING.string2base",
    "STRING.base2string",
    "STRING.string2int",
    "STRING.int2string",
    "STRING.chr",
    "STRING.ord",
    "STRING.token2string",
];

/// The code points of a stored string, each as its bytes.
fn units(value: &[u8]) -> Vec<&[u8]> {
    let mut units = Vec::new();
    for chunk in value.utf8_chunks() {
        let valid = chunk.valid();
        let mut offset = 0;
        for character in valid.chars() {
            let length = character.len_utf8();
            units.push(&valid.as_bytes()[offset..offset + length]);
            offset += length;
        }
        units.extend(chunk.invalid().chunks(1));
    }
    units
}

fn base_argument(draw: &mut Draw<'_>, env: &mut Env) -> Term {
    let base = draw.pick(&[2, 8, 10, 16, 36, 7, 1, 37, 0]);
    draw.int(base, env)
}

fn string_case(draw: &mut Draw<'_>) -> Case {
    let hook = draw.pick(&STRING_HOOKS);
    let mut env = Env::new();
    let env = &mut env;
    let arguments = match hook {
        "STRING.eq" | "STRING.ne" | "STRING.lt" | "STRING.le" | "STRING.gt" | "STRING.ge" => {
            let left = text_value(draw, 3);
            let right = match draw.below(4) {
                0 => left.clone(),
                1 => left[..draw.below(left.len() + 1)].to_vec(),
                _ => text_value(draw, 3),
            };
            vec![string(draw, env, left), string(draw, env, right)]
        }
        "STRING.concat" => vec![text(draw, env, 3), text(draw, env, 3)],
        "STRING.length" => vec![text(draw, env, 5)],
        "STRING.substr" => {
            let value = text_value(draw, 4);
            let length = units(&value).len();
            let (start, end) = (draw.index(length), draw.index(length));
            vec![
                string(draw, env, value),
                draw.int(start, env),
                draw.int(end, env),
            ]
        }
        "STRING.find" | "STRING.rfind" => {
            let haystack = text_value(draw, 5);
            let haystack_units = units(&haystack);
            // A needle taken from the haystack half of the time, or a prefix of one of its
            // code points that ends inside it, which matches bytes but no whole code point.
            let multibyte = (0..haystack_units.len())
                .filter(|&unit| haystack_units[unit].len() > 1)
                .collect::<Vec<_>>();
            let needle = match draw.below(4) {
                0 | 1 => {
                    let start = draw.below(haystack_units.len() + 1);
                    let end = start + draw.below(haystack_units.len() - start + 1);
                    haystack_units[start..end].concat()
                }
                2 if !multibyte.is_empty() => {
                    let unit = draw.pick(&multibyte);
                    let from = unit - draw.below(2).min(unit);
                    let mut needle = haystack_units[from..=unit].concat();
                    needle.pop();
                    needle
                }
                _ => text_value(draw, 2),
            };
            let start = draw.index(haystack_units.len());
            vec![
                string(draw, env, haystack),
                string(draw, env, needle),
                draw.int(start, env),
            ]
        }
        "STRING.string2base" => {
            let value = numeral(draw);
            vec![string(draw, env, value), base_argument(draw, env)]
        }
        "STRING.base2string" => {
            let value = small_int(draw);
            vec![draw.int(value, env), base_argument(draw, env)]
        }
        "STRING.string2int" => {
            let value = numeral(draw);
            vec![string(draw, env, value)]
        }
        "STRING.int2string" => {
            let value = small_int(draw);
            vec![draw.int(value, env)]
        }
        "STRING.chr" => {
            let value = match draw.below(3) {
                0 => BigInt::from(draw.below(0x11_0000)),
                _ => BigInt::from(draw.pick(&[
                    0_i64,
                    0x41,
                    0x7f,
                    0x80,
                    0xff,
                    0x100,
                    0xd7ff,
                    0xd800,
                    0xdfff,
                    0xe000,
                    0x10_ffff,
                    0x11_0000,
                    -1,
                    1 << 40,
                ])),
            };
            vec![draw.int(value, env)]
        }
        "STRING.ord" => vec![text(draw, env, 2)],
        "STRING.token2string" => {
            let value = text_value(draw, 3);
            vec![encode(&Val::Token("SortId".into(), value))]
        }
        _ => unreachable!(),
    };
    Case {
        hook,
        arguments,
        env: env.clone(),
    }
}

/// `[+-]?[0-9a-zA-Z]+` with every digit below `base`, read in that base.
fn read_numeral(text: &[u8], base: u32) -> Option<BigInt> {
    let (negative, digits) = match text.first() {
        Some(b'-') => (true, &text[1..]),
        Some(b'+') => (false, &text[1..]),
        _ => (false, text),
    };
    if digits.is_empty() {
        return None;
    }
    let mut value = BigInt::zero();
    for digit in digits {
        let digit = char::from(*digit)
            .to_digit(36)
            .filter(|digit| *digit < base)?;
        value = value * base + digit;
    }
    Some(if negative { -value } else { value })
}

fn digits(value: &BigInt, base: u32) -> String {
    if value.is_zero() {
        return "0".into();
    }
    let mut magnitude = value.abs();
    let mut text = Vec::new();
    while !magnitude.is_zero() {
        let digit = (&magnitude % base).to_u32().unwrap();
        text.push(char::from_digit(digit, base).unwrap());
        magnitude /= base;
    }
    if value.is_negative() {
        text.push('-');
    }
    text.iter().rev().collect()
}

fn string_model(hook: &str, arguments: &[Val]) -> Spec {
    use Val::{Bool, Int, Str, Token};
    // A stored string outside UTF-8 has no numeral or character reading; the textual
    // conversions may decline it.
    let textual = |text: &[u8], spec: Spec| {
        if std::str::from_utf8(text).is_ok() {
            spec
        } else {
            spec.declinable()
        }
    };
    match (hook, arguments) {
        // The natural lexicographic order of strings, by code point: the byte order of UTF-8.
        ("STRING.eq", [Str(left), Str(right)]) => Spec::value(Bool(left == right)),
        ("STRING.ne", [Str(left), Str(right)]) => Spec::value(Bool(left != right)),
        ("STRING.lt", [Str(left), Str(right)]) => Spec::value(Bool(left < right)),
        ("STRING.le", [Str(left), Str(right)]) => Spec::value(Bool(left <= right)),
        ("STRING.gt", [Str(left), Str(right)]) => Spec::value(Bool(left > right)),
        ("STRING.ge", [Str(left), Str(right)]) => Spec::value(Bool(left >= right)),
        ("STRING.concat", [Str(left), Str(right)]) => {
            Spec::value(Str(left.iter().chain(right).copied().collect()))
        }
        ("STRING.length", [Str(value)]) => Spec::value(Val::int(units(value).len())),
        // `[startIndex..endIndex)` on valid indices `0 <= start <= end <= length`. The symbol
        // is declared total, so outside them it has a value the documentation does not give.
        ("STRING.substr", [Str(value), Int(start), Int(end)]) => {
            let units = units(value);
            match at_most(end, units.len())
                .zip(start.to_usize())
                .filter(|(end, start)| start <= end)
            {
                Some((end, start)) => Spec::value(Str(units[start..end].concat())),
                None => Spec::unspecified(),
            }
        }
        // The first occurrence at or after `index` (`find`), or the last at or before it
        // (`rfind`), in code points; -1 if there is none. Every integer index is one: the
        // candidates are the code point positions on that side of it.
        ("STRING.find" | "STRING.rfind", [Str(haystack), Str(needle), Int(start)]) => {
            let units = units(haystack);
            let occurs =
                |from: usize| (from..=units.len()).any(|to| units[from..to].concat() == *needle);
            let positions = (0..=units.len()).filter(|&from| {
                let from = BigInt::from(from);
                if hook == "STRING.find" {
                    from >= *start
                } else {
                    from <= *start
                }
            });
            let found = if hook == "STRING.find" {
                positions.into_iter().find(|&from| occurs(from))
            } else {
                positions.into_iter().rfind(|&from| occurs(from))
            };
            Spec::value(Val::int(found.map_or(-1, |found| found as i64)))
        }
        ("STRING.string2base", [Str(text), Int(base)]) => {
            match base.to_u32().filter(|base| (2..=36).contains(base)) {
                Some(base) => textual(text, Spec::partial(read_numeral(text, base).map(Int))),
                None => Spec::open(),
            }
        }
        // Letters of either case, chosen consistently by the backend.
        ("STRING.base2string", [Int(value), Int(base)]) => {
            match base.to_u32().filter(|base| (2..=36).contains(base)) {
                Some(base) => {
                    let lower = digits(value, base);
                    Spec::one_of(vec![
                        Str(lower.to_uppercase().into_bytes()),
                        Str(lower.into_bytes()),
                    ])
                }
                None => Spec::open(),
            }
        }
        // A nonempty sequence of digits optionally prefixed by a sign.
        ("STRING.string2int", [Str(text)]) => {
            let decimal = text
                .iter()
                .all(|byte| byte.is_ascii_digit() || *byte == b'-' || *byte == b'+');
            textual(
                text,
                Spec::partial(read_numeral(text, 10).filter(|_| decimal).map(Int)),
            )
        }
        ("STRING.int2string", [Int(value)]) => Spec::value(Str(value.to_string().into_bytes())),
        // A string holding the one code point; no String holds a surrogate (KORE string
        // literals cannot) or a number outside the code points, so those are undefined.
        ("STRING.chr", [Int(value)]) => Spec::partial(
            value
                .to_u32()
                .and_then(char::from_u32)
                .map(|character| Str(character.to_string().into_bytes())),
        ),
        ("STRING.ord", [Str(text)]) => match units(text).as_slice() {
            [unit] => match std::str::from_utf8(unit) {
                Ok(character) => {
                    Spec::value(Val::int(u32::from(character.chars().next().unwrap())))
                }
                // A byte outside UTF-8 is a code point of the stored string, the one a `\xNN`
                // escape writes: U+00NN.
                Err(_) => Spec::value(Val::int(unit[0])),
            },
            _ => textual(text, Spec::bottom()),
        },
        ("STRING.token2string", [Token(_, text)]) => Spec::value(Str(text.clone())),
        _ => panic!("no STRING model for {hook} on {arguments:?}"),
    }
}

#[test]
fn string_hooks_agree_with_a_code_point_model() {
    let tallies = run(CASES, &string_case, &string_model);
    assert_reached(&tallies, &STRING_HOOKS, &[]);
}
