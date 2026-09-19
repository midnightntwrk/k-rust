//! String and quoted-label codecs used by textual KAST.

use std::fmt::Write;

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

/// Quote a concrete K String or Bytes payload without requiring UTF-8.
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

/// Decode a concrete K String or Bytes token into its exact byte payload.
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
        match escape {
            '"' => output.push(b'"'),
            '\\' => output.push(b'\\'),
            'n' => output.push(b'\n'),
            'r' => output.push(b'\r'),
            't' => output.push(b'\t'),
            'f' => output.push(0x0c),
            'x' => output.push(read_hex(&mut characters, 2)? as u8),
            'u' => push_scalar_utf8(&mut output, read_hex(&mut characters, 4)?)?,
            'U' => push_scalar_utf8(&mut output, read_hex(&mut characters, 8)?)?,
            digit @ '0'..='9' => {
                let mut digits = String::from(digit);
                digits.push(characters.next().ok_or("truncated octal escape")?);
                digits.push(characters.next().ok_or("truncated octal escape")?);
                let value = u16::from_str_radix(&digits, 8).map_err(|_| "invalid octal escape")?;
                output.push(u8::try_from(value).map_err(|_| "octal byte escape out of range")?);
            }
            _ => return Err("unsupported escape".into()),
        }
    }
    Ok(output)
}

fn read_hex(characters: &mut impl Iterator<Item = char>, digits: usize) -> Result<u32, String> {
    let value: String = characters.take(digits).collect();
    if value.len() != digits {
        return Err("truncated Unicode escape".into());
    }
    u32::from_str_radix(&value, 16).map_err(|_| "invalid Unicode escape".into())
}

fn push_scalar_utf8(output: &mut Vec<u8>, value: u32) -> Result<(), String> {
    let character = char::from_u32(value).ok_or("invalid Unicode scalar")?;
    let mut buffer = [0; 4];
    output.extend_from_slice(character.encode_utf8(&mut buffer).as_bytes());
    Ok(())
}

fn read_escape(characters: &mut impl Iterator<Item = char>, digits: usize) -> Result<char, String> {
    let value: String = characters.take(digits).collect();
    if value.len() != digits {
        return Err("truncated Unicode escape".into());
    }
    let value = u32::from_str_radix(&value, 16).map_err(|_| "invalid Unicode escape")?;
    char::from_u32(value).ok_or_else(|| "invalid Unicode scalar".into())
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
