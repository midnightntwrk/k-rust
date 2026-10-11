//! String and quoted-label codecs used by textual KAST.

use std::fmt::Write;

/// The escapes of a K `String` or `Bytes` literal that name a code point by a letter, as
/// (letter, code point): `\"`, `\\`, `\n`, `\r`, `\t` and `\f`.
pub const NAMED_ESCAPES: [(char, char); 6] = [
    ('"', '"'),
    ('\\', '\\'),
    ('n', '\n'),
    ('r', '\r'),
    ('t', '\t'),
    ('f', '\u{000c}'),
];

/// The escapes of a K literal that give a number in exactly so many hexadecimal digits, as
/// (letter, digits). In a `String` literal the number is a code point; in a `Bytes` literal a
/// number of at most [`BYTE_DIGITS`] digits is one byte, and a longer one a code point, which
/// contributes its UTF-8 encoding.
pub const HEX_ESCAPES: [(char, usize); 3] = [('x', 2), ('u', 4), ('U', 8)];

/// The most hexadecimal digits of a `Bytes` literal's escape that gives one byte.
pub const BYTE_DIGITS: usize = 2;

/// A backslash and a decimal digit begin an escape of this many octal digits, whose number is a
/// code point in a `String` literal and one byte in a `Bytes` literal.
pub const OCTAL_DIGITS: usize = 3;

pub fn quote(value: &str) -> String {
    let mut output = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            '\u{000c}' => output.push_str("\\f"),
            ' '..='~' => output.push(character),
            character if u32::from(character) <= 0xff => {
                write!(output, "\\x{:02x}", u32::from(character)).unwrap();
            }
            character if u32::from(character) <= 0xffff => {
                write!(output, "\\u{:04x}", u32::from(character)).unwrap();
            }
            character => {
                write!(output, "\\U{:08x}", u32::from(character)).unwrap();
            }
        }
    }
    output.push('"');
    output
}

/// Quote a concrete K `Bytes` payload.
///
/// Unlike [`quote`], this treats `\xNN` as an escape for one byte. Non-ASCII
/// bytes are always escaped so the result remains valid Rust and JSON text.
pub fn quote_bytes(value: &[u8]) -> String {
    let mut output = String::from("\"");
    for &byte in value {
        match byte {
            b'"' => output.push_str("\\\""),
            b'\\' => output.push_str("\\\\"),
            b'\n' => output.push_str("\\n"),
            b'\r' => output.push_str("\\r"),
            b'\t' => output.push_str("\\t"),
            0x0c => output.push_str("\\f"),
            b' '..=b'~' => output.push(char::from(byte)),
            byte => write!(output, "\\x{byte:02x}").unwrap(),
        }
    }
    output.push('"');
    output
}

pub fn unquote(input: &str) -> Result<String, String> {
    if !input.starts_with('"') || !input.ends_with('"') || input.len() < 2 {
        return Err("expected a double-quoted string".into());
    }
    let mut output = String::new();
    let mut characters = input[1..input.len() - 1].chars().peekable();
    while let Some(character) = characters.next() {
        if character != '\\' {
            output.push(character);
            continue;
        }
        let escape = characters.next().ok_or("truncated escape")?;
        match escape {
            '"' => output.push('"'),
            '\\' => output.push('\\'),
            'n' => output.push('\n'),
            'r' => output.push('\r'),
            't' => output.push('\t'),
            'f' => output.push('\u{000c}'),
            'x' => output.push(read_escape(&mut characters, 2)?),
            'u' => output.push(read_escape(&mut characters, 4)?),
            'U' => output.push(read_escape(&mut characters, 8)?),
            digit @ '0'..='9' => {
                let mut digits = String::from(digit);
                digits.push(characters.next().ok_or("truncated octal escape")?);
                digits.push(characters.next().ok_or("truncated octal escape")?);
                let value = u32::from_str_radix(&digits, 8).map_err(|_| "invalid octal escape")?;
                output.push(char::from_u32(value).ok_or("invalid octal scalar")?);
            }
            _ => {}
        }
    }
    Ok(output)
}

/// Decode a concrete K `String` token into its code points.
///
/// Every escape names one code point (`domains.md`): `\xFF` "a code point between 0x00 and
/// 0xff", `\uFFFF` and `\UFFFFFFFF` likewise, an octal `\NNN` its value; an unknown escape
/// is an error.
pub fn unquote_text(input: &str) -> Result<String, String> {
    if !input.starts_with('"') || !input.ends_with('"') || input.len() < 2 {
        return Err("expected a double-quoted string".into());
    }
    let mut output = String::new();
    let mut characters = input[1..input.len() - 1].chars().peekable();
    while let Some(character) = characters.next() {
        if character != '\\' {
            output.push(character);
            continue;
        }
        let escape = characters.next().ok_or("truncated escape")?;
        output.push(match escape_kind(escape)? {
            Escape::Named(character) => character,
            Escape::Hex(digits) => read_escape(&mut characters, digits)?,
            Escape::Octal => char::from_u32(read_octal(escape, &mut characters)?)
                .ok_or("invalid octal scalar")?,
        });
    }
    Ok(output)
}

/// Decode a concrete K `Bytes` token into its bytes.
///
/// `\xNN` contributes one byte. Direct Unicode and `\u`/`\U` escapes
/// contribute the scalar's UTF-8 encoding.
pub fn unquote_bytes(input: &str) -> Result<Vec<u8>, String> {
    if !input.starts_with('"') || !input.ends_with('"') || input.len() < 2 {
        return Err("expected a double-quoted string".into());
    }
    let mut output = Vec::new();
    let mut characters = input[1..input.len() - 1].chars().peekable();
    while let Some(character) = characters.next() {
        if character != '\\' {
            let mut buffer = [0; 4];
            output.extend_from_slice(character.encode_utf8(&mut buffer).as_bytes());
            continue;
        }
        let escape = characters.next().ok_or("truncated escape")?;
        match escape_kind(escape)? {
            Escape::Named(character) => output.push(
                u8::try_from(u32::from(character))
                    .expect("a named escape names an ASCII code point"),
            ),
            Escape::Hex(digits) if digits <= BYTE_DIGITS => output.push(
                u8::try_from(read_hex(&mut characters, digits)?)
                    .expect("two hexadecimal digits give a byte"),
            ),
            Escape::Hex(digits) => {
                push_scalar_utf8(&mut output, read_hex(&mut characters, digits)?)?
            }
            Escape::Octal => output.push(
                u8::try_from(read_octal(escape, &mut characters)?)
                    .map_err(|_| "octal byte escape out of range")?,
            ),
        }
    }
    Ok(output)
}

/// What a backslash followed by `escape` begins in a K literal.
enum Escape {
    /// A code point named by its letter.
    Named(char),
    /// A number in this many hexadecimal digits.
    Hex(usize),
    /// A number in [`OCTAL_DIGITS`] octal digits, of which `escape` is the first.
    Octal,
}

fn escape_kind(escape: char) -> Result<Escape, String> {
    if let Some((_, character)) = NAMED_ESCAPES.iter().find(|(letter, _)| *letter == escape) {
        Ok(Escape::Named(*character))
    } else if let Some((_, digits)) = HEX_ESCAPES.iter().find(|(letter, _)| *letter == escape) {
        Ok(Escape::Hex(*digits))
    } else if escape.is_ascii_digit() {
        Ok(Escape::Octal)
    } else {
        Err("unsupported escape".into())
    }
}

/// The number of the octal escape whose first digit is `first` and whose others follow.
fn read_octal(first: char, characters: &mut impl Iterator<Item = char>) -> Result<u32, String> {
    let mut value = 0;
    for index in 0..OCTAL_DIGITS {
        let digit = if index == 0 {
            first
        } else {
            characters.next().ok_or("truncated octal escape")?
        };
        value = value * 8 + digit.to_digit(8).ok_or("invalid octal escape")?;
    }
    Ok(value)
}

/// The number of the next `digits` hexadecimal digits.
fn read_hex(characters: &mut impl Iterator<Item = char>, digits: usize) -> Result<u32, String> {
    let mut value = 0;
    for _ in 0..digits {
        let digit = characters.next().ok_or("truncated Unicode escape")?;
        value = value * 16 + digit.to_digit(16).ok_or("invalid Unicode escape")?;
    }
    Ok(value)
}

fn push_scalar_utf8(output: &mut Vec<u8>, value: u32) -> Result<(), String> {
    let character = char::from_u32(value).ok_or("invalid Unicode scalar")?;
    let mut buffer = [0; 4];
    output.extend_from_slice(character.encode_utf8(&mut buffer).as_bytes());
    Ok(())
}

fn read_escape(characters: &mut impl Iterator<Item = char>, digits: usize) -> Result<char, String> {
    char::from_u32(read_hex(characters, digits)?).ok_or_else(|| "invalid Unicode scalar".into())
}

pub fn quote_label(value: &str) -> String {
    format!("`{}`", value.replace('\\', "\\\\").replace('`', "\\`"))
}

pub fn unquote_label(input: &str) -> Result<String, String> {
    if !input.starts_with('`') || !input.ends_with('`') || input.len() < 2 {
        return Err("expected a backtick-quoted label".into());
    }
    let mut output = String::new();
    let mut characters = input[1..input.len() - 1].chars();
    while let Some(character) = characters.next() {
        if character == '\\' {
            match characters.next().ok_or("truncated label escape")? {
                '\\' => output.push('\\'),
                '`' => output.push('`'),
                _ => return Err("unsupported label escape".into()),
            }
        } else if character.is_control() {
            return Err("control character in label".into());
        } else {
            output.push(character);
        }
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::{quote_bytes, unquote_bytes};

    #[test]
    fn byte_codec_round_trips_invalid_utf8_and_unicode() {
        for value in [vec![0xff, 0x80, 0x00, b'A'], "hé🙂".as_bytes().to_vec()] {
            assert_eq!(unquote_bytes(&quote_bytes(&value)).unwrap(), value);
        }
        assert_eq!(
            unquote_bytes(r#""\u03b1\U0001f642""#).unwrap(),
            "α🙂".as_bytes()
        );
    }
}
