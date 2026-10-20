//! Values as K text and as KORE, and K text read back as values (ARCHITECTURE 2.3, 2.6).
//! Owner: FZ-03 (builtin sorts); FZ-09 and FZ-G6 add collection and data-sort printing.
//!
//! The K text of a builtin value is a token in the lexical syntax the prelude declares for its
//! sort (`builtin/domains.md`):
//!
//! - `Int`: `[\+\-]?[0-9]+` (`INT-SYNTAX`);
//! - `Bool`: `true`, `false` (`BOOL-SYNTAX`);
//! - `String`: a double-quoted sequence of characters other than `"`, `\`, newline and carriage
//!   return, and of the escapes `\n \r \t \f \" \\`, `\xhh`, `\uhhhh` and `\Uhhhhhhhh`, each
//!   naming one code point (`STRING-SYNTAX`);
//! - `Bytes`: `b` and a double-quoted sequence of printable ASCII other than `"` and `\`, and of
//!   the escapes `\t \n \f \r \" \\` and `\xhh`, each naming one byte (`BYTES-SYNTAX`);
//! - `MInt{W}`: `[\+\-]?[0-9]+[pP][0-9]+`, a signed decimal reduced modulo `2^W` and the width
//!   (`MINT-SYNTAX`).
//!
//! The printer writes printable ASCII as itself and every other code point or byte as an
//! escape, so that the text is plain ASCII whatever the value.

use core::fmt::Write as _;

use k_rust::{
    kast::parser::parse_sort,
    kompile::encode_kore_sort,
    kore::ast::{KoreString, Pattern as KorePattern, Sort as KoreSort},
    names::{BuiltinSort, MINT_SORT},
};
use num_bigint::{BigInt, BigUint};

use super::{Value, ValueSort, check_shape};

/// Why a value cannot be printed as K text that parses back.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PrintError {
    /// The value's shape does not match the sort.
    SortMismatch,
    /// The sort has no printer in this milestone (collections before FZ-09, data sorts before
    /// G-6).
    Unsupported(String),
}

/// The refusal for collection values.
fn collections_unsupported() -> PrintError {
    PrintError::Unsupported("collection values are printed from FZ-09 (M3) on".to_owned())
}

/// The refusal for data-sort values.
fn data_unsupported() -> PrintError {
    PrintError::Unsupported("data-sort values are printed from FZ-G6 (G-6) on".to_owned())
}

/// `value` as K text at `sort`: the text a span hole's literal is replaced with
/// (ARCHITECTURE 2.3) and the witness's K text (2.6). For builtin sorts it is the literal the
/// definition's lexical syntax reads (`-5` for a negative `Int`, a quoted and escaped string,
/// `b"…"` for bytes, `5p64` for `MInt{64}`); a token is its text. Whether the program's grammar
/// reads it back as the intended value at the hole's position is FZ-02's round-trip check, not
/// this function's.
///
/// # Errors
///
/// [`PrintError`] when the value cannot be printed.
pub(crate) fn print_k_text(value: &Value, sort: &ValueSort) -> Result<String, PrintError> {
    check_shape(value, sort).map_err(|_| PrintError::SortMismatch)?;
    Ok(match value {
        Value::Int(number) => number.to_string(),
        Value::Bool(true) => "true".to_owned(),
        Value::Bool(false) => "false".to_owned(),
        Value::String(text) => quote_string(text),
        Value::Bytes(bytes) => quote_bytes(bytes),
        Value::MInt { width, value } => format!("{value}p{width}"),
        Value::Token { text, .. } => text.clone(),
        Value::List(_) | Value::Set(_) | Value::Map(_) => return Err(collections_unsupported()),
        Value::Apply { .. } => return Err(data_unsupported()),
    })
}

/// `value` as a KORE pattern of `sort` (a domain value `\dv{SortInt{}}("5")`, a collection
/// built from the collection's symbols, or a constructor application), not injected: the
/// expected term at a hole's position for the round-trip check (ARCHITECTURE 2.3), the
/// substitution of a KORE-template hole, and the witness's KORE (2.6).
///
/// A domain value's payload is the canonical text of its sort's kind: the decimal without `+`
/// or leading zeros for `Int`, the code points of a `String`, one code point per byte (the
/// byte's value) for `Bytes`, and the unsigned residue, `p` and the width at
/// `SortMInt{Sort<W>{}}` for `MInt{W}`.
///
/// # Errors
///
/// [`PrintError`] when the value's shape does not match the sort, or the sort has no printer.
pub(crate) fn to_kore(value: &Value, sort: &ValueSort) -> Result<KorePattern, PrintError> {
    check_shape(value, sort).map_err(|_| PrintError::SortMismatch)?;
    let builtin = |sort: BuiltinSort| KoreSort::Application {
        name: sort.kore_name().to_owned(),
        arguments: Vec::new(),
    };
    let (sort, payload) = match value {
        Value::Int(number) => (
            builtin(BuiltinSort::Int),
            KoreString::from(number.to_string()),
        ),
        Value::Bool(flag) => (
            builtin(BuiltinSort::Bool),
            KoreString::from(if *flag { "true" } else { "false" }),
        ),
        Value::String(text) => (
            builtin(BuiltinSort::String),
            KoreString::from(text.as_str()),
        ),
        Value::Bytes(bytes) => (builtin(BuiltinSort::Bytes), KoreString::from(bytes.clone())),
        Value::MInt { width, value } => (
            KoreSort::Application {
                name: MINT_SORT.to_owned(),
                arguments: vec![KoreSort::Application {
                    name: format!("Sort{width}"),
                    arguments: Vec::new(),
                }],
            },
            KoreString::from(format!("{value}p{width}")),
        ),
        Value::Token { sort, text } => {
            let kast = parse_sort(sort).map_err(|_| PrintError::SortMismatch)?;
            (encode_kore_sort(&kast), KoreString::from(text.as_str()))
        }
        Value::List(_) | Value::Set(_) | Value::Map(_) => return Err(collections_unsupported()),
        Value::Apply { .. } => return Err(data_unsupported()),
    };
    Ok(KorePattern::DomainValue {
        sort,
        value: payload,
    })
}

/// `text`, a K literal of `sort` in the lexical syntax of the module comment, as the value it
/// denotes: the inverse of [`print_k_text`], which also reads every other spelling the lexical
/// syntax admits (`+5`, `"A"`, `-1p8`). FZ-02 can read hole anchors with it.
///
/// # Errors
///
/// A message when `text` is not a literal of the sort, or the sort has no reader in this
/// milestone (collections, data sorts).
pub(crate) fn parse_k_text(text: &str, sort: &ValueSort) -> Result<Value, String> {
    match sort {
        ValueSort::Int => parse_int(text).map(Value::Int),
        ValueSort::Bool => match text {
            "true" => Ok(Value::Bool(true)),
            "false" => Ok(Value::Bool(false)),
            _ => Err(format!("{text:?} is not a Bool literal")),
        },
        ValueSort::String => unquote_string(text).map(Value::String),
        ValueSort::Bytes => text
            .strip_prefix('b')
            .ok_or_else(|| format!("{text:?} is not a Bytes literal: no leading `b`"))
            .and_then(unquote_bytes)
            .map(Value::Bytes),
        ValueSort::MInt { width } => parse_mint(text, *width),
        ValueSort::Token { sort } => {
            if text.is_empty() {
                Err("an empty token".to_owned())
            } else {
                Ok(Value::Token {
                    sort: sort.clone(),
                    text: text.to_owned(),
                })
            }
        }
        ValueSort::List { sort, .. }
        | ValueSort::Set { sort, .. }
        | ValueSort::Map { sort, .. } => {
            Err(format!("{sort} literals are read from FZ-09 (M3) on"))
        }
        ValueSort::Data { sort, .. } => Err(format!("{sort} terms are read from FZ-G6 on")),
    }
}

/// An `Int` literal, `[\+\-]?[0-9]+`.
fn parse_int(text: &str) -> Result<BigInt, String> {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(digits) => (true, digits),
        None => (false, text.strip_prefix('+').unwrap_or(text)),
    };
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!("{text:?} is not an Int literal"));
    }
    let magnitude: BigInt = digits
        .parse()
        .map_err(|_| format!("{text:?} is not an Int literal"))?;
    Ok(if negative { -magnitude } else { magnitude })
}

/// An `MInt{width}` literal, `[\+\-]?[0-9]+[pP][0-9]+`, whose suffix names `width`: its signed
/// decimal reduced modulo `2^width`.
fn parse_mint(text: &str, width: u32) -> Result<Value, String> {
    let not_literal = || format!("{text:?} is not an MInt{{{width}}} literal");
    let (number, suffix) = text.split_once(['p', 'P']).ok_or_else(not_literal)?;
    if suffix.is_empty() || !suffix.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(not_literal());
    }
    let named: BigUint = suffix.parse().map_err(|_| not_literal())?;
    if named != BigUint::from(width) {
        return Err(format!("{text:?} names width {named}, not {width}"));
    }
    let number = parse_int(number).map_err(|_| not_literal())?;
    let modulus = BigInt::from(1u8) << width;
    let residue = ((number % &modulus) + &modulus) % &modulus;
    Ok(Value::MInt {
        width,
        value: BigUint::try_from(residue).expect("a residue is non-negative"),
    })
}

/// `text` as a K `String` literal.
fn quote_string(text: &str) -> String {
    let mut output = String::with_capacity(text.len() + 2);
    output.push('"');
    for character in text.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            '\u{c}' => output.push_str("\\f"),
            ' '..='~' => output.push(character),
            _ => {
                let code = u32::from(character);
                let written = if code <= 0xff {
                    write!(output, "\\x{code:02x}")
                } else if code <= 0xffff {
                    write!(output, "\\u{code:04x}")
                } else {
                    write!(output, "\\U{code:08x}")
                };
                written.expect("writing to a String does not fail");
            }
        }
    }
    output.push('"');
    output
}

/// `bytes` as a K `Bytes` literal.
fn quote_bytes(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(bytes.len() + 3);
    output.push_str("b\"");
    for &byte in bytes {
        match byte {
            b'"' => output.push_str("\\\""),
            b'\\' => output.push_str("\\\\"),
            b'\n' => output.push_str("\\n"),
            b'\r' => output.push_str("\\r"),
            b'\t' => output.push_str("\\t"),
            0x0c => output.push_str("\\f"),
            b' '..=b'~' => output.push(char::from(byte)),
            _ => write!(output, "\\x{byte:02x}").expect("writing to a String does not fail"),
        }
    }
    output.push('"');
    output
}

/// The text between the quotes of a literal `text`.
fn between_quotes(text: &str) -> Result<&str, String> {
    text.strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
        .ok_or_else(|| format!("{text:?} is not a double-quoted literal"))
}

/// The number written in the next `digits` hexadecimal digits of `characters`.
fn hex(characters: &mut core::str::Chars<'_>, digits: usize) -> Result<u32, String> {
    let mut value = 0u32;
    for _ in 0..digits {
        let digit = characters
            .next()
            .and_then(|character| character.to_digit(16))
            .ok_or_else(|| format!("an escape needs {digits} hexadecimal digits"))?;
        value = value * 16 + digit;
    }
    Ok(value)
}

/// The code points of a K `String` literal.
fn unquote_string(text: &str) -> Result<String, String> {
    let mut characters = between_quotes(text)?.chars();
    let mut output = String::new();
    while let Some(character) = characters.next() {
        match character {
            '"' | '\n' | '\r' => {
                return Err(format!("{character:?} must be escaped in a String literal"));
            }
            '\\' => {
                let escape = characters.next().ok_or("a truncated escape")?;
                let code = match escape {
                    'n' => u32::from('\n'),
                    'r' => u32::from('\r'),
                    't' => u32::from('\t'),
                    'f' => 0x0c,
                    '"' | '\\' => u32::from(escape),
                    'x' => hex(&mut characters, 2)?,
                    'u' => hex(&mut characters, 4)?,
                    'U' => hex(&mut characters, 8)?,
                    _ => return Err(format!("`\\{escape}` is not a String escape")),
                };
                output.push(
                    char::from_u32(code)
                        .ok_or_else(|| format!("U+{code:X} is not a code point"))?,
                );
            }
            _ => output.push(character),
        }
    }
    Ok(output)
}

/// The bytes of a K `Bytes` literal without its `b`.
fn unquote_bytes(text: &str) -> Result<Vec<u8>, String> {
    let mut characters = between_quotes(text)?.chars();
    let mut output = Vec::new();
    while let Some(character) = characters.next() {
        match character {
            '\\' => {
                let escape = characters.next().ok_or("a truncated escape")?;
                output.push(match escape {
                    'n' => b'\n',
                    'r' => b'\r',
                    't' => b'\t',
                    'f' => 0x0c,
                    '"' => b'"',
                    '\\' => b'\\',
                    'x' => u8::try_from(hex(&mut characters, 2)?)
                        .expect("two hexadecimal digits give a byte"),
                    _ => return Err(format!("`\\{escape}` is not a Bytes escape")),
                });
            }
            ' ' | '!' | '#'..='[' | ']'..='~' => {
                output.push(u8::try_from(character).expect("printable ASCII is one byte"));
            }
            _ => {
                return Err(format!("{character:?} must be escaped in a Bytes literal"));
            }
        }
    }
    Ok(output)
}
