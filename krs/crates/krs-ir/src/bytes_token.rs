//! Canonical transport spelling for compiler-owned Bytes tokens.

use std::fmt;

/// Encodes bytes as a `b"` token with one lowercase `\xHH` escape per byte.
#[must_use]
pub fn encode(bytes: &[u8]) -> String {
    use fmt::Write as _;

    let mut token = String::with_capacity(3 + bytes.len() * 4);
    token.push_str("b\"");
    for byte in bytes {
        write!(&mut token, "\\x{byte:02x}").expect("writing to a String cannot fail");
    }
    token.push('"');
    token
}

/// Decodes only the canonical spelling produced by [`encode`].
///
/// # Errors
///
/// Returns [`InvalidBytesToken`] if the framing, escape, or hex digit is invalid.
pub fn decode(token: &str) -> Result<Vec<u8>, InvalidBytesToken> {
    let body = token
        .strip_prefix("b\"")
        .and_then(|body| body.strip_suffix('"'))
        .ok_or(InvalidBytesToken)?;
    let (chunks, remainder) = body.as_bytes().as_chunks::<4>();
    if !remainder.is_empty() {
        return Err(InvalidBytesToken);
    }

    chunks
        .iter()
        .map(|chunk| {
            if chunk[0] != b'\\' || chunk[1] != b'x' {
                return Err(InvalidBytesToken);
            }
            let high = nibble(chunk[2]).ok_or(InvalidBytesToken)?;
            let low = nibble(chunk[3]).ok_or(InvalidBytesToken)?;
            Ok((high << 4) | low)
        })
        .collect()
}

/// Spells bytes as a program writes them: the token K's `kprint` prints for a Bytes value
/// (`krs-unparse`'s `enquote` after a `b`), each printable ASCII byte as itself, `\\`, `\"`,
/// `\n`, `\t`, `\r` and `\f` escaped, and every other byte `\xHH`. A program's parse keeps a
/// Bytes token as it is written, and static expansion compares tokens as written, so a static
/// clause's subject holds the token in this spelling, which a program writing the value as KRS
/// prints it matches (`b"ab"`, where the transport spelling is `b"\x61\x62"`).
#[must_use]
pub fn program_spelling(bytes: &[u8]) -> String {
    use fmt::Write as _;

    let mut token = String::with_capacity(3 + bytes.len());
    token.push_str("b\"");
    for &byte in bytes {
        match byte {
            b'\\' => token.push_str("\\\\"),
            b'"' => token.push_str("\\\""),
            b'\n' => token.push_str("\\n"),
            b'\t' => token.push_str("\\t"),
            b'\r' => token.push_str("\\r"),
            b'\x0c' => token.push_str("\\f"),
            32..=126 => token.push(char::from(byte)),
            _ => write!(&mut token, "\\x{byte:02x}").expect("writing to a String cannot fail"),
        }
    }
    token.push('"');
    token
}

fn nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

/// A Bytes token that is not in canonical transport form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidBytesToken;

impl fmt::Display for InvalidBytesToken {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("invalid canonical Bytes token")
    }
}

impl std::error::Error for InvalidBytesToken {}

#[cfg(test)]
mod tests {
    use super::{decode, encode, program_spelling};

    #[test]
    fn a_program_spells_printable_bytes_as_themselves() {
        assert_eq!(program_spelling(b"ab"), r#"b"ab""#);
        assert_eq!(program_spelling(&[]), r#"b"""#);
        assert_eq!(
            program_spelling(b"a\"\\\n\t\r\x0c\x01\xc3"),
            r#"b"a\"\\\n\t\r\f\x01\xc3""#
        );
    }

    #[test]
    fn bytes_tokens_accept_only_canonical_lower_hex_transport() {
        assert_eq!(decode(r#"b"\x00\x7f\xff""#).unwrap(), [0, 127, 255]);

        for malformed in [
            r#""\x00""#,
            r#"b"00""#,
            r#"b"\x0""#,
            r#"b"\xGG""#,
            r#"b"\xAF""#,
            r#"b"\x+1""#,
            r#"b"\u{00}""#,
            r#"b"\x00"#,
        ] {
            assert!(decode(malformed).is_err(), "accepted {malformed}");
        }
    }

    #[test]
    fn bytes_tokens_round_trip_empty_and_every_byte() {
        assert_eq!(encode(&[]), r#"b"""#);
        assert!(decode(&encode(&[])).unwrap().is_empty());

        let bytes = (u8::MIN..=u8::MAX).collect::<Vec<_>>();
        assert_eq!(decode(&encode(&bytes)).unwrap(), bytes);
        assert_eq!(encode(&[0, 65, 255]), r#"b"\x00\x41\xff""#);
    }
}
