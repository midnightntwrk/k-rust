//! KORE string quoting and unquoting.

use std::fmt;

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

pub fn unquote(input: &str) -> Result<String, StringError> {
    if !input.starts_with('"') {
        return Err(error(0, "expected opening quote"));
    }
    if input.len() < 2 || !input.ends_with('"') {
        return Err(error(input.len(), "expected closing quote"));
    }

    let body = &input[1..input.len() - 1];
    let mut result = String::new();
    let mut offset = 0;
    while offset < body.len() {
        let character = body[offset..].chars().next().expect("offset is in bounds");
        if character != '\\' {
            result.push(character);
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
            '"' => result.push('"'),
            '\\' => result.push('\\'),
            'n' => result.push('\n'),
            'r' => result.push('\r'),
            't' => result.push('\t'),
            'f' => result.push('\u{c}'),
            'x' => result.push(read_escape(body, &mut offset, 2, escape_offset)?),
            'u' => result.push(read_escape(body, &mut offset, 4, escape_offset)?),
            'U' => result.push(read_escape(body, &mut offset, 8, escape_offset)?),
            // This intentionally matches scala-kore StringUtil: unknown escapes
            // discard the backslash and preserve the following character.
            other => result.push(other),
        }
    }
    Ok(result)
}

pub fn quote(value: &str) -> String {
    let mut result = String::with_capacity(value.len() + 2);
    result.push('"');
    for character in value.chars() {
        match character {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '\u{c}' => result.push_str("\\f"),
            character if character.is_ascii_graphic() || character == ' ' => result.push(character),
            character if character <= '\u{ff}' => {
                result.push_str(&format!("\\x{:02x}", character as u32));
            }
            character if character <= '\u{ffff}' => {
                result.push_str(&format!("\\u{:04x}", character as u32));
            }
            character => result.push_str(&format!("\\U{:08x}", character as u32)),
        }
    }
    result.push('"');
    result
}

fn read_escape(
    body: &str,
    offset: &mut usize,
    digits: usize,
    escape_offset: usize,
) -> Result<char, StringError> {
    let end = offset.saturating_add(digits);
    let Some(hex) = body.get(*offset..end) else {
        return Err(error(escape_offset, "truncated Unicode escape"));
    };
    let codepoint =
        u32::from_str_radix(hex, 16).map_err(|_| error(escape_offset, "invalid Unicode escape"))?;
    let character = char::from_u32(codepoint)
        .ok_or_else(|| error(escape_offset, "invalid Unicode scalar value"))?;
    *offset = end;
    Ok(character)
}

const fn error(offset: usize, message: &'static str) -> StringError {
    StringError { offset, message }
}
