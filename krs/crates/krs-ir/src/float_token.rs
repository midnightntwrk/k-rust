//! Canonical spelling of K `Float` tokens.
//!
//! K 7.1.337 has one `Float` sort, and every value carries its precision and
//! exponent range in its token (`domains.md`, Floats): no suffix and `d` are
//! IEEE binary64 (53 bits of precision, 11 exponent bits), `f` is binary32
//! (24, 8), and `pNxM` is N bits of precision with M exponent bits.
//!
//! KRS spells a Rust float literal as one K token, keeping its digits (without
//! `_` separators) and its sign: no suffix stays unsuffixed, `f64` becomes `d`,
//! `f32` becomes `f`, and K's own `pNxM` suffix is kept. The constants
//! `f64::NAN`, `f64::INFINITY`, and `f64::NEG_INFINITY` are `NaN`, `Infinity`,
//! and `-Infinity`, and their `f32` forms take the `f` suffix. NaN has no sign
//! in K's token syntax, so a negated NaN has no spelling.
//!
//! [`validate`] accepts exactly the tokens these rules produce. Each lexes back
//! through `FLOAT-SYNTAX` as the same Float: a numeric token always has a
//! fraction, an exponent, or a suffix, so it is never an `Int` token.

use std::fmt;

/// The precision and exponent range of IEEE binary32 (`f32`, K suffix `f`).
pub const BINARY32: FloatFormat = FloatFormat {
    precision: 24,
    exponent_bits: 8,
};

/// The precision and exponent range of IEEE binary64 (`f64`, K's default).
pub const BINARY64: FloatFormat = FloatFormat {
    precision: 53,
    exponent_bits: 11,
};

/// Precision and exponent range of a K Float value.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FloatFormat {
    /// Bits of precision, including the implicit bit.
    pub precision: u32,
    /// Bits of exponent range.
    pub exponent_bits: u32,
}

impl FloatFormat {
    /// Whether this is IEEE binary32 or binary64, the formats every route evaluates.
    #[must_use]
    pub const fn is_binary32_or_binary64(self) -> bool {
        matches!((self.precision, self.exponent_bits), (24, 8) | (53, 11))
    }
}

/// A Rust float constant path `f32::NAME` or `f64::NAME`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FloatConstant {
    /// `NAN`.
    Nan,
    /// `INFINITY`.
    Infinity,
    /// `NEG_INFINITY`.
    NegInfinity,
}

impl FloatConstant {
    /// The constant named `name` under `f32::` or `f64::`.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "NAN" => Some(Self::Nan),
            "INFINITY" => Some(Self::Infinity),
            "NEG_INFINITY" => Some(Self::NegInfinity),
            _ => None,
        }
    }

    /// The Rust constant name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Nan => "NAN",
            Self::Infinity => "INFINITY",
            Self::NegInfinity => "NEG_INFINITY",
        }
    }
}

/// Rust float type of a constant path or suffix.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FloatWidth {
    /// `f32`, K suffix `f`.
    F32,
    /// `f64`; K's default, so its constants take no suffix.
    F64,
}

impl FloatWidth {
    /// The width named by the Rust type `name` (`f32` or `f64`).
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "f32" => Some(Self::F32),
            "f64" => Some(Self::F64),
            _ => None,
        }
    }

    /// The Rust type name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::F32 => "f32",
            Self::F64 => "f64",
        }
    }
}

/// Why a Rust float literal or constant has no K Float token.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FloatLiteralError {
    /// A suffix other than `f32`, `f64`, or `pNxM`.
    Suffix,
    /// A `pNxM` suffix with a zero or a leading zero in N or M.
    PrecisionSuffix,
    /// A minus on `NAN`.
    NegatedNan,
    /// A minus on `INFINITY`.
    NegatedInfinity,
    /// A minus on `NEG_INFINITY`.
    NegatedNegInfinity,
    /// Digits that are not a decimal Rust float.
    Digits,
}

impl fmt::Display for FloatLiteralError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Suffix => {
                "Float literal suffix must be f32, f64, or K's p<precision>x<exponent>"
            }
            Self::PrecisionSuffix => {
                "a p<precision>x<exponent> suffix takes two positive decimal numbers without leading zeros"
            }
            Self::NegatedNan => "NaN has no sign in K's token syntax; write f64::NAN or f32::NAN",
            Self::NegatedInfinity => "write f64::NEG_INFINITY (or f32::NEG_INFINITY)",
            Self::NegatedNegInfinity => "write f64::INFINITY (or f32::INFINITY)",
            Self::Digits => "Float literals must be decimal Rust float literals",
        })
    }
}

impl std::error::Error for FloatLiteralError {}

/// The token of a Rust numeric literal with `digits` (separators allowed),
/// float `suffix` (empty for none), and an optional leading minus.
///
/// # Errors
///
/// Returns the reason the literal has no K Float spelling.
pub fn from_literal(
    negative: bool,
    digits: &str,
    suffix: &str,
) -> Result<String, FloatLiteralError> {
    let digits = digits.replace('_', "");
    let k_suffix = match suffix {
        "" => String::new(),
        "f32" => "f".to_owned(),
        "f64" => "d".to_owned(),
        other => {
            precision_suffix(other)?;
            other.to_owned()
        }
    };
    if !is_mantissa(&digits) || (k_suffix.is_empty() && !has_fraction_or_exponent(&digits)) {
        return Err(FloatLiteralError::Digits);
    }
    let sign = if negative { "-" } else { "" };
    Ok(format!("{sign}{digits}{k_suffix}"))
}

/// The token of the Rust constant `width::constant`, optionally negated.
///
/// # Errors
///
/// Returns the reason a negated constant has no K Float spelling.
pub fn from_constant(
    width: FloatWidth,
    constant: FloatConstant,
    negative: bool,
) -> Result<String, FloatLiteralError> {
    let value = match (constant, negative) {
        (FloatConstant::Nan, false) => "NaN",
        (FloatConstant::Infinity, false) => "Infinity",
        (FloatConstant::NegInfinity, false) => "-Infinity",
        (FloatConstant::Nan, true) => return Err(FloatLiteralError::NegatedNan),
        (FloatConstant::Infinity, true) => return Err(FloatLiteralError::NegatedInfinity),
        (FloatConstant::NegInfinity, true) => return Err(FloatLiteralError::NegatedNegInfinity),
    };
    let suffix = match width {
        FloatWidth::F32 => "f",
        FloatWidth::F64 => "",
    };
    Ok(format!("{value}{suffix}"))
}

/// A token that is not the canonical spelling of a Rust float literal or constant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidFloatToken;

impl fmt::Display for InvalidFloatToken {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("not a canonical K Float token")
    }
}

impl std::error::Error for InvalidFloatToken {}

/// Checks that `token` is a canonical Float token and returns its format.
///
/// # Errors
///
/// Returns [`InvalidFloatToken`] for anything [`from_literal`] and
/// [`from_constant`] cannot produce.
pub fn validate(token: &str) -> Result<FloatFormat, InvalidFloatToken> {
    match token {
        "NaN" | "Infinity" | "-Infinity" => return Ok(BINARY64),
        "NaNf" | "Infinityf" | "-Infinityf" => return Ok(BINARY32),
        _ => {}
    }
    let unsigned = token.strip_prefix('-').unwrap_or(token);
    let end = unsigned
        .find(|character: char| !matches!(character, '0'..='9' | '.' | 'e' | 'E' | '+' | '-'))
        .unwrap_or(unsigned.len());
    let (mantissa, suffix) = unsigned.split_at(end);
    if !is_mantissa(mantissa) {
        return Err(InvalidFloatToken);
    }
    match suffix {
        "" if has_fraction_or_exponent(mantissa) => Ok(BINARY64),
        "d" => Ok(BINARY64),
        "f" => Ok(BINARY32),
        other => precision_suffix(other).map_err(|_| InvalidFloatToken),
    }
}

/// Rust spelling of a canonical Float token, for the reference layer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RustFloat {
    /// One Rust literal token, possibly negative, such as `-0.0` or `0.1f32`.
    Literal(String),
    /// A constant path `width::constant`.
    Constant(FloatWidth, FloatConstant),
}

/// The Rust spelling that KRS reads back as `token`.
///
/// # Errors
///
/// Returns [`InvalidFloatToken`] when `token` is not canonical.
pub fn rust_spelling(token: &str) -> Result<RustFloat, InvalidFloatToken> {
    validate(token)?;
    let constant = |width, constant| Ok(RustFloat::Constant(width, constant));
    match token {
        "NaN" => return constant(FloatWidth::F64, FloatConstant::Nan),
        "NaNf" => return constant(FloatWidth::F32, FloatConstant::Nan),
        "Infinity" => return constant(FloatWidth::F64, FloatConstant::Infinity),
        "Infinityf" => return constant(FloatWidth::F32, FloatConstant::Infinity),
        "-Infinity" => return constant(FloatWidth::F64, FloatConstant::NegInfinity),
        "-Infinityf" => return constant(FloatWidth::F32, FloatConstant::NegInfinity),
        _ => {}
    }
    let literal = if let Some(digits) = token.strip_suffix('f') {
        format!("{digits}f32")
    } else if let Some(digits) = token.strip_suffix('d') {
        format!("{digits}f64")
    } else {
        token.to_owned()
    };
    Ok(RustFloat::Literal(literal))
}

/// `[0-9]+(\.[0-9]*)?([eE][+-]?[0-9]+)?`, the Rust-producible part of K's
/// Float mantissa.
fn is_mantissa(text: &str) -> bool {
    let (number, exponent) = match text.find(['e', 'E']) {
        Some(index) => (&text[..index], Some(&text[index + 1..])),
        None => (text, None),
    };
    let (integer, fraction) = match number.split_once('.') {
        Some((integer, fraction)) => (integer, Some(fraction)),
        None => (number, None),
    };
    let digits = |text: &str| text.bytes().all(|byte| byte.is_ascii_digit());
    !integer.is_empty()
        && digits(integer)
        && fraction.is_none_or(digits)
        && exponent.is_none_or(|exponent| {
            let exponent = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
            !exponent.is_empty() && digits(exponent)
        })
}

fn has_fraction_or_exponent(mantissa: &str) -> bool {
    mantissa.contains(['.', 'e', 'E'])
}

/// Parses `pNxM`: [`FloatLiteralError::Suffix`] when the text is not of that
/// shape, [`FloatLiteralError::PrecisionSuffix`] when N or M is zero or has a
/// leading zero.
fn precision_suffix(suffix: &str) -> Result<FloatFormat, FloatLiteralError> {
    let (precision, exponent_bits) = suffix
        .strip_prefix('p')
        .and_then(|rest| rest.split_once('x'))
        .ok_or(FloatLiteralError::Suffix)?;
    let number = |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
    if !number(precision) || !number(exponent_bits) {
        return Err(FloatLiteralError::Suffix);
    }
    let positive = |text: &str| {
        if text.starts_with('0') {
            None
        } else {
            text.parse::<u32>().ok()
        }
    };
    positive(precision)
        .zip(positive(exponent_bits))
        .map(|(precision, exponent_bits)| FloatFormat {
            precision,
            exponent_bits,
        })
        .ok_or(FloatLiteralError::PrecisionSuffix)
}

#[cfg(test)]
mod tests {
    use super::{
        BINARY32, BINARY64, FloatConstant, FloatFormat, FloatLiteralError, FloatWidth, RustFloat,
        from_constant, from_literal, rust_spelling, validate,
    };

    #[test]
    fn literal_mapping_table() {
        for (negative, digits, suffix, token) in [
            (false, "1.5", "", "1.5"),
            (false, "1.5", "f64", "1.5d"),
            (false, "0.1", "f32", "0.1f"),
            (false, "1", "f32", "1f"),
            (false, "1.0", "p113x15", "1.0p113x15"),
            (true, "0.0", "", "-0.0"),
            (false, "1_000.5", "", "1000.5"),
            (false, "1e10", "", "1e10"),
            (false, "2.5E-3", "f32", "2.5E-3f"),
            (false, "1.", "", "1."),
        ] {
            assert_eq!(from_literal(negative, digits, suffix).as_deref(), Ok(token));
            assert!(validate(token).is_ok(), "{token}");
            let rust = rust_spelling(token).unwrap();
            let RustFloat::Literal(rust) = rust else {
                panic!("{token} is not a literal")
            };
            let unsigned = rust.strip_prefix('-').unwrap_or(&rust);
            let digits_end = unsigned
                .find(|character: char| {
                    character.is_ascii_alphabetic() && !matches!(character, 'e' | 'E')
                })
                .unwrap_or(unsigned.len());
            let (rust_digits, rust_suffix) = unsigned.split_at(digits_end);
            assert_eq!(
                from_literal(rust.starts_with('-'), rust_digits, rust_suffix).as_deref(),
                Ok(token)
            );
        }
    }

    #[test]
    fn constant_mapping_table() {
        for (width, constant, token) in [
            (FloatWidth::F64, FloatConstant::Nan, "NaN"),
            (FloatWidth::F32, FloatConstant::Nan, "NaNf"),
            (FloatWidth::F64, FloatConstant::Infinity, "Infinity"),
            (FloatWidth::F32, FloatConstant::Infinity, "Infinityf"),
            (FloatWidth::F64, FloatConstant::NegInfinity, "-Infinity"),
            (FloatWidth::F32, FloatConstant::NegInfinity, "-Infinityf"),
        ] {
            assert_eq!(from_constant(width, constant, false).as_deref(), Ok(token));
            assert_eq!(
                rust_spelling(token),
                Ok(RustFloat::Constant(width, constant))
            );
        }
        assert_eq!(
            from_constant(FloatWidth::F64, FloatConstant::Nan, true),
            Err(FloatLiteralError::NegatedNan)
        );
        assert_eq!(
            from_constant(FloatWidth::F32, FloatConstant::Infinity, true),
            Err(FloatLiteralError::NegatedInfinity)
        );
        assert_eq!(
            from_constant(FloatWidth::F64, FloatConstant::NegInfinity, true),
            Err(FloatLiteralError::NegatedNegInfinity)
        );
    }

    #[test]
    fn rejected_suffixes() {
        for suffix in [
            "f16", "f128", "d", "u8", "P24X8", "p24", "x8", "p24x", "px8",
        ] {
            assert_eq!(
                from_literal(false, "1.0", suffix),
                Err(FloatLiteralError::Suffix),
                "{suffix}"
            );
        }
        for suffix in ["p0x8", "p24x0", "p024x8", "p24x08"] {
            assert_eq!(
                from_literal(false, "1.0", suffix),
                Err(FloatLiteralError::PrecisionSuffix),
                "{suffix}"
            );
        }
        assert_eq!(from_literal(false, "1", ""), Err(FloatLiteralError::Digits));
    }

    #[test]
    fn formats_follow_the_suffix() {
        assert_eq!(validate("1.5"), Ok(BINARY64));
        assert_eq!(validate("1.5d"), Ok(BINARY64));
        assert_eq!(validate("0.1f"), Ok(BINARY32));
        assert_eq!(validate("NaNf"), Ok(BINARY32));
        assert_eq!(
            validate("1.0p113x15"),
            Ok(FloatFormat {
                precision: 113,
                exponent_bits: 15
            })
        );
        assert!(BINARY32.is_binary32_or_binary64());
        assert!(!validate("1.0p113x15").unwrap().is_binary32_or_binary64());
    }

    #[test]
    fn non_canonical_tokens_are_invalid() {
        for token in [
            "",
            "1",
            "-1",
            "+1.0",
            ".5",
            "1.0D",
            "1.0F",
            "NaNd",
            "-NaN",
            "Infinityd",
            "1.0p0x8",
            "1.0e",
            "1.0q",
            "1__0.0",
            "--1.0",
        ] {
            assert!(validate(token).is_err(), "{token}");
        }
    }
}
