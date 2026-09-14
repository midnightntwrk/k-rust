//! Java `ModuleToKORE`'s KORE identifier encoding and its inverse, with the `Lbl`/`Sort`/`Var`
//! prefixes.
//!
//! ASCII alphanumerics and `-` pass through; every other UTF-16 unit becomes a four-letter
//! mnemonic from [`TABLE`] or four hex digits, and a run of encoded units shares one pair of
//! apostrophes. The eight KORE keywords get a `'Kywd'` suffix so they lex as identifiers.
//! `decode(encode(name)) == name` for every name; the backend's `external_variable_name` is a
//! different encoding (one escape per character, hex by scalar value) and is not this one.

use std::fmt::{self, Display, Formatter};

use crate::kore::ast::VariableKind;

/// The prefix of an encoded K label in KORE (`Lbl_+_` is `Lbl'UndsPlusUnds'`).
const LABEL_PREFIX: &str = "Lbl";
/// The prefix of an encoded K sort in KORE (`Sort` followed by the encoded sort name).
const SORT_PREFIX: &str = "Sort";
/// The prefix of an encoded K variable in KORE; a set variable carries the KORE `@` sigil first.
const VARIABLE_PREFIX: &str = "Var";
const SET_VARIABLE_SIGIL: char = '@';

/// KORE keywords a K name may spell; encoded with the `Kywd` code appended.
const KEYWORDS: [&str; 8] = [
    "module",
    "endmodule",
    "sort",
    "hooked-sort",
    "symbol",
    "hooked-symbol",
    "alias",
    "axiom",
];
const KEYWORD_CODE: &str = "Kywd";

/// The mnemonic for each encodable ASCII unit; `encode` indexes it by unit, `decode` by code.
/// Java's table also lists `-` for itself, but `-` is an identifier unit that is never encoded
/// and a one-character code can never match a four-character slot, so that row is dead in both
/// directions and is not carried.
const TABLE: [(u16, &str); 32] = [
    (0x20, "Spce"),
    (0x21, "Bang"),
    (0x22, "Quot"),
    (0x23, "Hash"),
    (0x24, "Dolr"),
    (0x25, "Perc"),
    (0x26, "And-"),
    (0x27, "Apos"),
    (0x28, "LPar"),
    (0x29, "RPar"),
    (0x2a, "Star"),
    (0x2b, "Plus"),
    (0x2c, "Comm"),
    (0x2e, "Stop"),
    (0x2f, "Slsh"),
    (0x3a, "Coln"),
    (0x3b, "SCln"),
    (0x3c, "-LT-"),
    (0x3d, "Eqls"),
    (0x3e, "-GT-"),
    (0x3f, "Ques"),
    (0x40, "-AT-"),
    (0x5b, "LSqB"),
    (0x5c, "Bash"),
    (0x5d, "RSqB"),
    (0x5e, "Xor-"),
    (0x5f, "Unds"),
    (0x60, "BQuo"),
    (0x7b, "LBra"),
    (0x7c, "Pipe"),
    (0x7d, "RBra"),
    (0x7e, "Tild"),
];

/// Why an encoded identifier does not decode.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DecodeError {
    /// The hex units between one pair of apostrophes are not valid UTF-16.
    InvalidUtf16 { encoded: String },
    /// An apostrophe-delimited run ends before a four-character code is complete.
    Truncated { encoded: String },
    /// A four-character code is neither hex nor a mnemonic.
    UnknownCode { code: String },
    /// An apostrophe opened a run that never closed.
    Unterminated { encoded: String },
    /// A KORE sort name without the `Sort` prefix.
    MissingSortPrefix { encoded: String },
}

impl Display for DecodeError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidUtf16 { encoded } => {
                write!(
                    formatter,
                    "invalid UTF-16 in encoded identifier {encoded:?}"
                )
            }
            Self::Truncated { encoded } => {
                write!(formatter, "truncated encoded identifier {encoded:?}")
            }
            Self::UnknownCode { code } => {
                write!(formatter, "unknown KORE identifier code {code:?}")
            }
            Self::Unterminated { encoded } => {
                write!(formatter, "unterminated encoded identifier {encoded:?}")
            }
            Self::MissingSortPrefix { encoded } => {
                write!(
                    formatter,
                    "compound KORE sort {encoded:?} lacks Sort prefix"
                )
            }
        }
    }
}

impl std::error::Error for DecodeError {}

/// Encode a K name with Java `ModuleToKORE`'s KORE identifier encoding.
pub fn encode(name: &str) -> String {
    if KEYWORDS.contains(&name) {
        return format!("{name}'{KEYWORD_CODE}'");
    }
    let mut encoded = String::new();
    let mut in_identifier = true;
    for unit in name.encode_utf16() {
        if is_identifier_unit(unit) {
            if !in_identifier {
                encoded.push('\'');
                in_identifier = true;
            }
            encoded.push(char::from_u32(u32::from(unit)).expect("ASCII identifier unit"));
        } else {
            if in_identifier {
                encoded.push('\'');
                in_identifier = false;
            }
            if let Some(mnemonic) = mnemonic(unit) {
                encoded.push_str(mnemonic);
            } else {
                use std::fmt::Write;
                write!(encoded, "{unit:04x}").expect("writing to a string cannot fail");
            }
        }
    }
    if !in_identifier {
        encoded.push('\'');
    }
    encoded
}

/// Decode a KORE identifier produced by [`encode`] back to the K name.
pub fn decode(encoded: &str) -> Result<String, DecodeError> {
    let mut output = String::new();
    let mut encoded_units = Vec::new();
    let mut literal = true;
    let mut offset = 0;
    while offset < encoded.len() {
        let character = encoded[offset..].chars().next().unwrap();
        if character == '\'' {
            if !literal {
                output.push_str(&String::from_utf16(&encoded_units).map_err(|_| {
                    DecodeError::InvalidUtf16 {
                        encoded: encoded.to_owned(),
                    }
                })?);
                encoded_units.clear();
            }
            literal = !literal;
            offset += 1;
        } else if literal {
            output.push(character);
            offset += character.len_utf8();
        } else {
            let end = offset + 4;
            let code = encoded
                .get(offset..end)
                .ok_or_else(|| DecodeError::Truncated {
                    encoded: encoded.to_owned(),
                })?;
            if let Ok(unit) = u16::from_str_radix(code, 16) {
                encoded_units.push(unit);
            } else if code != KEYWORD_CODE {
                encoded_units.push(unit_for_code(code).ok_or_else(|| {
                    DecodeError::UnknownCode {
                        code: code.to_owned(),
                    }
                })?);
            }
            offset = end;
        }
    }
    if literal {
        Ok(output)
    } else {
        Err(DecodeError::Unterminated {
            encoded: encoded.to_owned(),
        })
    }
}

/// `Lbl` followed by the encoded label name.
pub fn encode_label(name: &str) -> String {
    format!("{LABEL_PREFIX}{}", encode(name))
}

/// The K label of a KORE symbol name; the `Lbl` prefix is optional because the prelude's own
/// symbols (`inj`, `kseq`, …) carry none.
pub fn decode_label(encoded: &str) -> Result<String, DecodeError> {
    decode(encoded.strip_prefix(LABEL_PREFIX).unwrap_or(encoded))
}

/// `Sort` followed by the encoded sort name.
pub fn encode_sort_name(name: &str) -> String {
    format!("{SORT_PREFIX}{}", encode(name))
}

/// The K sort name of a KORE sort name; the `Sort` prefix is required.
pub fn decode_sort_name(encoded: &str) -> Result<String, DecodeError> {
    let name = encoded
        .strip_prefix(SORT_PREFIX)
        .ok_or_else(|| DecodeError::MissingSortPrefix {
            encoded: encoded.to_owned(),
        })?;
    decode(name)
}

/// `Var` (or `@Var` for a set variable) followed by the encoded variable name.
pub fn encode_variable(name: &str, kind: VariableKind) -> String {
    match kind {
        VariableKind::Element => format!("{VARIABLE_PREFIX}{}", encode(name)),
        VariableKind::Set => format!("{SET_VARIABLE_SIGIL}{VARIABLE_PREFIX}{}", encode(name)),
    }
}

/// The kind and K name of a KORE variable name; a leading `@` marks a set variable and the
/// `Var` prefix is optional.
pub fn decode_variable(encoded: &str) -> (VariableKind, Result<String, DecodeError>) {
    let (kind, name) = encoded
        .strip_prefix(SET_VARIABLE_SIGIL)
        .map_or((VariableKind::Element, encoded), |name| {
            (VariableKind::Set, name)
        });
    let name = name.strip_prefix(VARIABLE_PREFIX).unwrap_or(name);
    (kind, decode(name))
}

fn is_identifier_unit(unit: u16) -> bool {
    (unit <= u16::from(u8::MAX) && char::from(unit as u8).is_ascii_alphanumeric())
        || unit == u16::from(b'-')
}

/// [`TABLE`] indexed by unit, so `encode` does one array read per encoded unit.
const MNEMONICS: [Option<&str>; 128] = {
    let mut mnemonics = [None; 128];
    let mut index = 0;
    while index < TABLE.len() {
        mnemonics[TABLE[index].0 as usize] = Some(TABLE[index].1);
        index += 1;
    }
    mnemonics
};

fn mnemonic(unit: u16) -> Option<&'static str> {
    MNEMONICS.get(usize::from(unit)).copied().flatten()
}

fn unit_for_code(code: &str) -> Option<u16> {
    TABLE
        .iter()
        .find(|(_, mnemonic)| *mnemonic == code)
        .map(|(unit, _)| *unit)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encodes_java_kore_identifier_edge_cases() {
        assert_eq!(encode("_+_"), "'UndsPlusUnds'");
        assert_eq!(
            encode("<generatedTop>-fragment"),
            "'-LT-'generatedTop'-GT-'-fragment"
        );
        assert_eq!(encode("_|->_"), "'UndsPipe'-'-GT-Unds'");
        assert_eq!(encode("module"), "module'Kywd'");
        assert_eq!(encode("éα"), "'00e903b1'");
        assert_eq!(encode("😀"), "'d83dde00'");
        assert_eq!(encode("\n"), "'000a'");
    }
}
