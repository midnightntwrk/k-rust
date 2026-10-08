//! Canonical spelling of K `String` tokens.
//!
//! A K 7.1.337 String is a sequence of code points in U+0000..=U+00FF
//! (`domains.md`, Strings). KRS spells each value one way, as a token that
//! `STRING-SYNTAX`'s regular expression lexes back to the same value: printable
//! ASCII verbatim except `"` as `\"` and `\` as `\\`; newline, carriage return,
//! tab, and form feed as `\n`, `\r`, `\t`, `\f`; every other code point as a
//! lowercase `\xHH`.

use std::fmt;

/// The largest code point a K String holds.
pub const MAX_CODE_POINT: char = '\u{ff}';

/// Encodes a value as its canonical quoted token.
///
/// # Errors
///
/// Returns [`StringOutOfRange`] with the first code point above U+00FF.
pub fn encode(value: &str) -> Result<String, StringOutOfRange> {
    use fmt::Write as _;

    let mut token = String::with_capacity(value.len() + 2);
    token.push('"');
    for character in value.chars() {
        match character {
            '"' => token.push_str("\\\""),
            '\\' => token.push_str("\\\\"),
            '\n' => token.push_str("\\n"),
            '\r' => token.push_str("\\r"),
            '\t' => token.push_str("\\t"),
            '\u{c}' => token.push_str("\\f"),
            ' '..='~' => token.push(character),
            character if character <= MAX_CODE_POINT => {
                write!(&mut token, "\\x{:02x}", u32::from(character))
                    .expect("writing to a String cannot fail");
            }
            character => return Err(StringOutOfRange(character)),
        }
    }
    token.push('"');
    Ok(token)
}

/// Decodes only the canonical spelling produced by [`encode`].
///
/// # Errors
///
/// Returns [`InvalidStringToken`] if the token is not the canonical spelling
/// of its value.
pub fn decode(token: &str) -> Result<String, InvalidStringToken> {
    let body = token
        .strip_prefix('"')
        .and_then(|body| body.strip_suffix('"'))
        .ok_or(InvalidStringToken)?;
    let mut value = String::with_capacity(body.len());
    let mut characters = body.chars();
    while let Some(character) = characters.next() {
        if character != '\\' {
            value.push(character);
            continue;
        }
        let decoded = match characters.next().ok_or(InvalidStringToken)? {
            '"' => '"',
            '\\' => '\\',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            'f' => '\u{c}',
            'x' => {
                let high = characters
                    .next()
                    .and_then(nibble)
                    .ok_or(InvalidStringToken)?;
                let low = characters
                    .next()
                    .and_then(nibble)
                    .ok_or(InvalidStringToken)?;
                char::from((high << 4) | low)
            }
            _ => return Err(InvalidStringToken),
        };
        value.push(decoded);
    }
    if encode(&value).as_deref() == Ok(token) {
        Ok(value)
    } else {
        Err(InvalidStringToken)
    }
}

fn nibble(character: char) -> Option<u8> {
    match character {
        '0'..='9' => Some(character as u8 - b'0'),
        'a'..='f' => Some(character as u8 - b'a' + 10),
        _ => None,
    }
}

/// A value holding a code point that a K String cannot hold.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StringOutOfRange(pub char);

impl fmt::Display for StringOutOfRange {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "code point U+{:04X} is above U+00FF, the largest a K String holds",
            u32::from(self.0)
        )
    }
}

impl std::error::Error for StringOutOfRange {}

/// A String token that is not in canonical form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidStringToken;

impl fmt::Display for InvalidStringToken {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("invalid canonical String token")
    }
}

impl std::error::Error for InvalidStringToken {}

#[cfg(test)]
mod tests {
    use super::{InvalidStringToken, StringOutOfRange, decode, encode};

    #[test]
    fn values_round_trip_through_their_canonical_token() {
        for (value, token) in [
            ("", r#""""#),
            ("plain text", r#""plain text""#),
            ("say \"hi\"", r#""say \"hi\"""#),
            ("a\\b", r#""a\\b""#),
            ("line\nbreak\r\t\u{c}", r#""line\nbreak\r\t\f""#),
            ("\u{0}\u{1f}\u{7f}", r#""\x00\x1f\x7f""#),
            ("\u{c1}\u{ff}", r#""\xc1\xff""#),
        ] {
            assert_eq!(encode(value).unwrap(), token, "{value:?}");
            assert_eq!(decode(token).unwrap(), value, "{token}");
        }
    }

    #[test]
    fn code_points_above_latin_1_are_out_of_range() {
        assert_eq!(encode("\u{100}"), Err(StringOutOfRange('\u{100}')));
        assert_eq!(encode("ok \u{1f600}"), Err(StringOutOfRange('\u{1f600}')));
    }

    #[test]
    fn only_canonical_tokens_decode() {
        for token in [
            "unquoted",
            r#""\q""#,
            r#""\x4""#,
            r#""\xC1""#,
            r#""\x41""#,
            r#""Á""#,
            "\"\u{c1}\"",
            "\"tab\tin token\"",
            r#""trailing\""#,
        ] {
            assert_eq!(decode(token), Err(InvalidStringToken), "{token}");
        }
    }
}
