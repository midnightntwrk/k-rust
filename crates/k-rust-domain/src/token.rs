//! The value a token denotes, by which two spellings of one value are one term.
//!
//! A token of a sort with domain values denotes the domain value the emitted definition reads
//! from its text: an element of its hook's domain, which the backend stores as its canonical
//! text ([`DomainKind`]). So two spellings of one value are one term: the integers `1`, `+1` and
//! `01`; the strings `"a"` and `"\x61"`; the byte strings `b"ab"` and `b"\x61\x62"`; the floats
//! `1.5`, `1.50` and `15e-1`, which name one binary64 number. A float's format is part of its
//! value (`1.5f` is a binary32 number, another value than `1.5`), as is its sign at zero (`0.0`
//! and `-0.0` are two values, though `==Float` holds of them), and the literal syntax names one
//! NaN per format, which is equal to itself as a term. A token of a sort whose domain values are
//! their texts (an unhooked token sort), of a sort without domain values, or whose text names no
//! value of its sort, denotes its text.
//!
//! Program expansion compares tokens by [`token_value`] over the emitted definition's
//! declarations; a compiler that writes terms over K's prelude, whose declarations it does not
//! hold, compares them by [`prelude_token_value`], the same value under the prelude's hooks.

use crate::kind::{BYTES_SORT, DomainKind, DomainSort, is_nullary};
use crate::string::{unquote_bytes, unquote_text};
use crate::text::{canonical_text, validate_text};

/// The value a token denotes ([`token_value`]): two tokens of one sort are one term exactly when
/// their values are equal, or, when neither has one, their texts are. A value holds the
/// canonical payload only, not its sort, so compare values only within one sort.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TokenValue(Box<[u8]>);

impl TokenValue {
    /// A text that names this value and no other value of its sort: the payload of its
    /// canonical domain value, its bytes in hexadecimal. Two tokens of one sort have one key
    /// exactly when they denote one value. It is a key to compare or index by, not a token.
    pub fn key(&self) -> String {
        self.0.iter().map(|byte| format!("{byte:02x}")).collect()
    }
}

/// The value the token `text` of `sort` denotes in a definition that declares `sort`'s head with
/// the hook `hook` and with domain values exactly when `has_domain_values`: the domain value the
/// emitted definition reads from the text, whose payload is its kind's canonical text. `None`
/// when the sort has no domain values or the text names no value of it; the token then denotes
/// its text.
///
/// The work is that of reading the value: for a float of a format other than binary32 and
/// binary64, exact big-integer arithmetic on its digits. A caller comparing many tokens keeps
/// each token's value rather than reading it per comparison.
pub fn token_value<S: DomainSort>(
    sort: &S,
    hook: Option<&str>,
    has_domain_values: bool,
    text: &str,
) -> Option<TokenValue> {
    let kind = DomainKind::of_declared_sort(sort, has_domain_values, hook)?;
    let payload = token_payload(text, hook, is_nullary(sort, BYTES_SORT)).ok()?;
    validate_text(kind, sort, &payload).ok()?;
    let canonical = canonical_text(kind, sort, &payload).map_or(payload, String::into_bytes);
    Some(TokenValue(canonical.into()))
}

/// The payload of the domain value the token `token` of a sort hooked `hook` writes: a `String`
/// token's code points and a `Bytes` token's bytes, unquoted, and any other token's text. The
/// payload holds code points as their UTF-8, or, when `bytes` (the sort `SortBytes`, whose
/// literals write each byte as the code point of its value), one byte per code point; there a
/// code point above U+00FF names no byte.
pub fn token_payload(token: &str, hook: Option<&str>, bytes: bool) -> Result<Vec<u8>, String> {
    let text = match hook {
        Some("STRING.String") => unquote_text(token)?,
        Some("BYTES.Bytes") => {
            let value = token
                .strip_prefix('b')
                .ok_or_else(|| "expected a leading `b`".to_owned())
                .and_then(unquote_bytes)?;
            if bytes {
                return Ok(value);
            }
            value.into_iter().map(char::from).collect()
        }
        _ => token.to_owned(),
    };
    if !bytes {
        return Ok(text.into_bytes());
    }
    text.chars()
        .map(|character| u8::try_from(u32::from(character)).ok())
        .collect::<Option<Vec<u8>>>()
        .ok_or_else(|| {
            format!("a code point above U+00FF in a value of {BYTES_SORT}, whose values are bytes")
        })
}

/// [`token_value`] for the nullary sort `name` of K's prelude (`domains.md`), under the hook the
/// prelude declares it with ([`prelude_hook`]); `None` for any other sort, whose tokens denote
/// their texts. The sort's KORE name is `Sort` followed by `name`.
pub fn prelude_token_value(name: &str, text: &str) -> Option<TokenValue> {
    let hook = prelude_hook(name, 0)?;
    token_value(&Nullary(format!("Sort{name}")), Some(hook), true, text)
}

/// Whether the tokens `left` and `right` of the nullary sort `name` of K's prelude denote one
/// value ([`prelude_token_value`]): equal texts, or equal values.
pub fn same_prelude_token(name: &str, left: &str, right: &str) -> bool {
    left == right
        || matches!(
            (prelude_token_value(name, left), prelude_token_value(name, right)),
            (Some(left), Some(right)) if left == right
        )
}

/// The hook K's prelude (`domains.md`) declares the sort `name` of `arity` parameters with, for
/// the sorts whose tokens have values other than their texts: `Int`, `Bool`, `Float`, `String`,
/// `Bytes` and `MInt{W}`.
pub fn prelude_hook(name: &str, arity: usize) -> Option<&'static str> {
    Some(match (name, arity) {
        ("Int", 0) => "INT.Int",
        ("Bool", 0) => "BOOL.Bool",
        ("Float", 0) => "FLOAT.Float",
        ("String", 0) => "STRING.String",
        ("Bytes", 0) => "BYTES.Bytes",
        ("MInt", 1) => "MINT.MInt",
        _ => return None,
    })
}

/// A nullary sort, by its KORE name.
struct Nullary(String);

impl DomainSort for Nullary {
    fn as_application(&self) -> Option<(&str, &[Self])> {
        Some((&self.0, &[]))
    }
}

#[cfg(test)]
mod tests {
    use super::same_prelude_token;

    #[test]
    fn prelude_tokens_are_compared_by_value() {
        for (left, right, same) in [
            ("1.5", "1.50", true),
            ("1.5", "15e-1", true),
            ("1.5", "1.5d", true),
            ("1.5", "1.5f", false),
            ("1.5f", "1.50f", true),
            ("0.0", "-0.0", false),
            ("0.0", "0e10", true),
            ("1.0p11x5", "1.00p11x5", true),
            ("1.0p11x5", "1.0p11x6", false),
            ("NaN", "NaN", true),
            ("NaNf", "NaN", false),
        ] {
            assert_eq!(
                same_prelude_token("Float", left, right),
                same,
                "{left} {right}"
            );
        }
        assert!(same_prelude_token("Int", "01", "1"));
        assert!(same_prelude_token("Int", "-0", "0"));
        assert!(!same_prelude_token("Int", "1", "-1"));
        assert!(same_prelude_token("String", "\"\\x61\"", "\"a\""));
        assert!(same_prelude_token("Bytes", "b\"\\x61\"", "b\"a\""));
        assert!(!same_prelude_token("Id", "x", "y"));
    }
}
