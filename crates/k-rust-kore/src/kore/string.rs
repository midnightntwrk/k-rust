//! KORE string quoting and unquoting.
//!
//! A KORE string literal is a sequence of code points (`kore-syntax.md`): printable ASCII stands
//! for itself, and every escape names one code point, `\xhh` the code point U+00hh. A
//! [`KoreString`] stores those code points by [`LiteralEncoding`]: one byte per code point for a
//! domain value of the sort `SortBytes`, whose code points are its bytes' values, and their UTF-8
//! encoding for every other literal.

use std::fmt;

use super::ast::{KoreString, Sort};
use crate::names::BuiltinSort;

/// How a [`KoreString`] stores the code points of a literal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LiteralEncoding {
    /// The UTF-8 encoding of the code points: string patterns and the domain values of every
    /// sort but `SortBytes`.
    Utf8,
    /// One byte per code point, the code point's value: the domain values of `SortBytes`, the
    /// sort hooked to `BYTES.Bytes`, whose literals write each byte as the code point of its
    /// value. A code point above U+00FF names no byte.
    Bytes,
}

impl LiteralEncoding {
    /// The encoding of a domain value of `sort`.
    pub fn of_domain_value(sort: &Sort) -> Self {
        match sort {
            Sort::Application { name, arguments }
                if arguments.is_empty() && name == BuiltinSort::Bytes.kore_name() =>
            {
                Self::Bytes
            }
            Sort::Application { .. } | Sort::Variable(_) => Self::Utf8,
        }
    }
}

/// The code points of a byte sequence read as text: each valid UTF-8 sequence is its code point,
/// and a byte that begins none is the code point of its value. A stored `Utf8` payload is valid
/// UTF-8, so this is its exact reading; it is also how bytes from outside a literal (console
/// input, a binary KORE payload) become a string.
pub fn text_from_bytes(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len());
    for chunk in bytes.utf8_chunks() {
        text.push_str(chunk.valid());
        text.extend(chunk.invalid().iter().map(|byte| char::from(*byte)));
    }
    text
}

/// `value`, a payload of `encoding`, as a payload holding the same code points in that encoding:
/// unchanged when it is one already, and otherwise, for `Utf8`, with each byte that begins no
/// UTF-8 sequence read as the code point of its value ([`text_from_bytes`]).
pub fn canonical(value: KoreString, encoding: LiteralEncoding) -> KoreString {
    match encoding {
        LiteralEncoding::Bytes => value,
        LiteralEncoding::Utf8 if value.as_utf8().is_ok() => value,
        LiteralEncoding::Utf8 => KoreString::from(text_from_bytes(value.as_bytes())),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StringError {
    pub offset: usize,
    pub message: &'static str,
}

impl fmt::Display for StringError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at byte {}", self.message, self.offset)
    }
}

impl std::error::Error for StringError {}

/// The code points of the literal `input` stored as UTF-8 (a string pattern, or a domain value of
/// a sort other than `SortBytes`).
pub fn unquote(input: &str) -> Result<KoreString, StringError> {
    unquote_as(input, LiteralEncoding::Utf8)
}

/// The code points of the literal `input` stored by `encoding`; in a `Bytes` literal a code point
/// above U+00FF is an error, since it names no byte.
pub fn unquote_as(input: &str, encoding: LiteralEncoding) -> Result<KoreString, StringError> {
    if !input.starts_with('"') {
        return Err(error(0, "expected opening quote"));
    }
    if input.len() < 2 || !input.ends_with('"') {
        return Err(error(input.len(), "expected closing quote"));
    }

    let body = &input[1..input.len() - 1];
    let mut result = Vec::new();
    let mut push = |character: char, at: usize| match encoding {
        LiteralEncoding::Utf8 => {
            let mut encoded = [0; 4];
            result.extend_from_slice(character.encode_utf8(&mut encoded).as_bytes());
            Ok(())
        }
        LiteralEncoding::Bytes => u8::try_from(u32::from(character))
            .map(|byte| result.push(byte))
            .map_err(|_| error(at, "code point above U+00FF in a Bytes literal")),
    };
    let mut offset = 0;
    while offset < body.len() {
        let character = body[offset..].chars().next().expect("offset is in bounds");
        if character != '\\' {
            if character.is_control() {
                return Err(error(offset, "non-printable character in string"));
            }
            push(character, offset)?;
            offset += character.len_utf8();
            continue;
        }

        let escape_offset = offset + 1;
        offset += 1;
        let Some(escape) = body[offset..].chars().next() else {
            return Err(error(escape_offset, "truncated escape"));
        };
        offset += escape.len_utf8();
        let character = match escape {
            '"' => '"',
            '\\' => '\\',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            'f' => '\u{c}',
            'x' => read_code_point(body, &mut offset, 2, escape_offset)?,
            'u' => read_code_point(body, &mut offset, 4, escape_offset)?,
            'U' => read_code_point(body, &mut offset, 8, escape_offset)?,
            _ => return Err(error(escape_offset, "unknown escape")),
        };
        push(character, escape_offset)?;
    }
    Ok(KoreString::from(result))
}

/// The literal of `value`, a UTF-8 payload (a string pattern, or a domain value of a sort other
/// than `SortBytes`).
pub fn quote(value: &KoreString) -> String {
    quote_as(value, LiteralEncoding::Utf8)
}

/// The literal of `value`, a payload of `encoding`: printable ASCII as itself, `\" \\ \n \r
/// \t \f`, a code point up to U+00FF as `\xhh`, up to U+FFFF as `\uhhhh`, and any other as
/// `\Uhhhhhhhh`. A `Utf8` payload that is not UTF-8 is read by [`text_from_bytes`].
pub fn quote_as(value: &KoreString, encoding: LiteralEncoding) -> String {
    let mut result = String::with_capacity(value.as_bytes().len() + 2);
    result.push('"');
    match encoding {
        LiteralEncoding::Bytes => {
            for byte in value.as_bytes() {
                push_quoted(&mut result, char::from(*byte));
            }
        }
        LiteralEncoding::Utf8 => match value.as_utf8() {
            Ok(text) => text
                .chars()
                .for_each(|character| push_quoted(&mut result, character)),
            Err(_) => text_from_bytes(value.as_bytes())
                .chars()
                .for_each(|character| push_quoted(&mut result, character)),
        },
    }
    result.push('"');
    result
}

fn push_quoted(result: &mut String, character: char) {
    use std::fmt::Write as _;
    match character {
        '"' => result.push_str("\\\""),
        '\\' => result.push_str("\\\\"),
        '\n' => result.push_str("\\n"),
        '\r' => result.push_str("\\r"),
        '\t' => result.push_str("\\t"),
        '\u{c}' => result.push_str("\\f"),
        ' '..='~' => result.push(character),
        character => {
            let code_point = u32::from(character);
            let _ = if code_point <= 0xff {
                write!(result, "\\x{code_point:02x}")
            } else if code_point <= 0xffff {
                write!(result, "\\u{code_point:04x}")
            } else {
                write!(result, "\\U{code_point:08x}")
            };
        }
    }
}

/// The code point of the `digits` hexadecimal digits at `offset`, which it advances past them.
fn read_code_point(
    body: &str,
    offset: &mut usize,
    digits: usize,
    escape_offset: usize,
) -> Result<char, StringError> {
    let end = offset.saturating_add(digits);
    let Some(hex) = body.get(*offset..end) else {
        return Err(error(escape_offset, "truncated Unicode escape"));
    };
    let code_point =
        u32::from_str_radix(hex, 16).map_err(|_| error(escape_offset, "invalid Unicode escape"))?;
    let character = char::from_u32(code_point)
        .ok_or_else(|| error(escape_offset, "invalid Unicode scalar value"))?;
    *offset = end;
    Ok(character)
}

const fn error(offset: usize, message: &'static str) -> StringError {
    StringError { offset, message }
}
