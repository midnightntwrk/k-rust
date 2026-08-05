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
