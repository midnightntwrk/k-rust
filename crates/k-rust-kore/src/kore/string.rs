//! KORE string quoting and unquoting.

use std::fmt;

use super::ast::KoreString;

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

pub fn unquote(input: &str) -> Result<KoreString, StringError> {
    if !input.starts_with('"') {
        return Err(error(0, "expected opening quote"));
    }
    if input.len() < 2 || !input.ends_with('"') {
        return Err(error(input.len(), "expected closing quote"));
    }

    let body = &input[1..input.len() - 1];
    let mut result = Vec::new();
    let mut offset = 0;
    while offset < body.len() {
        let character = body[offset..].chars().next().expect("offset is in bounds");
        if character != '\\' {
            if character.is_control() {
                return Err(error(offset, "non-printable character in string"));
            }
            let mut encoded = [0; 4];
            result.extend_from_slice(character.encode_utf8(&mut encoded).as_bytes());
            offset += character.len_utf8();
            continue;
        }

        let escape_offset = offset + 1;
        offset += 1;
        let Some(escape) = body[offset..].chars().next() else {
            return Err(error(escape_offset, "truncated escape"));
        };
        offset += escape.len_utf8();
        match escape {
            '"' => result.push(b'"'),
            '\\' => result.push(b'\\'),
            'n' => result.push(b'\n'),
            'r' => result.push(b'\r'),
            't' => result.push(b'\t'),
            'f' => result.push(0x0c),
            'x' => result.push(read_byte_escape(body, &mut offset, escape_offset)?),
            'u' => push_unicode_escape(body, &mut offset, 4, escape_offset, &mut result)?,
            'U' => push_unicode_escape(body, &mut offset, 8, escape_offset, &mut result)?,
            _ => return Err(error(escape_offset, "unknown escape")),
        }
    }
    Ok(KoreString::from(result))
}

pub fn quote(value: &KoreString) -> String {
    let mut result = String::with_capacity(value.as_bytes().len() + 2);
    result.push('"');
    for byte in value.as_bytes() {
        match *byte {
            b'"' => result.push_str("\\\""),
            b'\\' => result.push_str("\\\\"),
            b'\n' => result.push_str("\\n"),
            b'\r' => result.push_str("\\r"),
            b'\t' => result.push_str("\\t"),
            0x0c => result.push_str("\\f"),
            byte if byte.is_ascii_graphic() || byte == b' ' => result.push(char::from(byte)),
            byte => result.push_str(&format!("\\x{byte:02x}")),
        }
    }
    result.push('"');
    result
}

fn read_byte_escape(
    body: &str,
    offset: &mut usize,
    escape_offset: usize,
) -> Result<u8, StringError> {
    let end = offset.saturating_add(2);
    let Some(hex) = body.get(*offset..end) else {
        return Err(error(escape_offset, "truncated Unicode escape"));
    };
    let byte =
        u8::from_str_radix(hex, 16).map_err(|_| error(escape_offset, "invalid Unicode escape"))?;
    *offset = end;
    Ok(byte)
}

fn push_unicode_escape(
    body: &str,
    offset: &mut usize,
    digits: usize,
    escape_offset: usize,
    result: &mut Vec<u8>,
) -> Result<(), StringError> {
    let end = offset.saturating_add(digits);
    let Some(hex) = body.get(*offset..end) else {
        return Err(error(escape_offset, "truncated Unicode escape"));
    };
    let codepoint =
        u32::from_str_radix(hex, 16).map_err(|_| error(escape_offset, "invalid Unicode escape"))?;
    let character = char::from_u32(codepoint)
        .ok_or_else(|| error(escape_offset, "invalid Unicode scalar value"))?;
    let mut encoded = [0; 4];
    result.extend_from_slice(character.encode_utf8(&mut encoded).as_bytes());
    *offset = end;
    Ok(())
}

const fn error(offset: usize, message: &'static str) -> StringError {
    StringError { offset, message }
}
