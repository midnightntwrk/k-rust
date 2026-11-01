//! The `Float` literals of K's prelude: their lexical syntax (`domains.md`, FLOAT-SYNTAX), the
//! format a literal's suffix names, and the canonical text of the value a literal denotes
//! ([`canonical_float_text`]), which the backend's Float hooks also write for binary32 and
//! binary64.

use std::fmt;

use num_bigint::BigUint;
use num_traits::{One, Zero};

mod canonical;
#[cfg(any(test, feature = "rounding-model"))]
pub mod rounding_model;

pub use canonical::{
    FloatTextRefusal, MAX_FLOAT_CANONICAL_BITS, canonical_float_text, float_canonical_bits_estimate,
};

/// A Float format `pNxM`: `N` bits of precision and `M` exponent bits, both positive integers
/// (`domains.md`, "Floating-point numbers"). The fields are compared as numbers, so `p053x011`
/// is binary64. The backend computes binary32 (`p24x8`) and binary64 (`p53x11`); the definition
/// gives values in every other format too, which this backend does not compute.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FloatFormat {
    pub precision: BigUint,
    pub exponent_bits: BigUint,
}

impl FloatFormat {
    /// The format of these fields; `None` when either is 0, which names no format.
    pub fn new(precision: BigUint, exponent_bits: BigUint) -> Option<Self> {
        (!precision.is_zero() && !exponent_bits.is_zero()).then_some(Self {
            precision,
            exponent_bits,
        })
    }

    /// The format of these nonzero fields.
    pub fn of(precision: u32, exponent_bits: u32) -> Self {
        Self {
            precision: precision.into(),
            exponent_bits: exponent_bits.into(),
        }
    }

    fn is(&self, precision: u32, exponent_bits: u32) -> bool {
        self.precision == BigUint::from(precision)
            && self.exponent_bits == BigUint::from(exponent_bits)
    }

    /// Whether this is binary32, `p24x8`.
    pub fn is_binary32(&self) -> bool {
        self.is(24, 8)
    }

    /// Whether this is binary64, `p53x11`.
    pub fn is_binary64(&self) -> bool {
        self.is(53, 11)
    }

    /// Whether the backend computes this format: binary32 or binary64.
    pub fn is_computed(&self) -> bool {
        self.is_binary32() || self.is_binary64()
    }

    /// A field of 1: a format without IEEE-like parameters (no trailing significand bit, or
    /// `emin > emax`), which this backend does not compute even from the suffix.
    pub fn has_a_field_of_one(&self) -> bool {
        self.precision.is_one() || self.exponent_bits.is_one()
    }

    /// Whether every value of `other` is a value of this format: at least its precision and its
    /// exponent range.
    pub fn contains(&self, other: &Self) -> bool {
        self.precision >= other.precision && self.exponent_bits >= other.exponent_bits
    }
}

impl fmt::Display for FloatFormat {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "p{}x{} (precision {}, {} exponent bits)",
            self.precision, self.exponent_bits, self.precision, self.exponent_bits
        )
    }
}

/// The body of `token`, a text in FLOAT-SYNTAX ([`is_float_syntax`]), and the format its suffix
/// names: none, `d` or `D` is binary64, `f` or `F` binary32, and `pNxM` the format `pNxM`, its
/// fields read as unbounded integers; `None` for the format when a field is 0, which names no
/// format, so the token names no Float.
pub fn split_token(token: &str) -> (&str, Option<FloatFormat>) {
    let digits = |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
    let explicit = token
        .rsplit_once(['x', 'X'])
        .and_then(|(rest, exponent_bits)| Some((rest.rsplit_once(['p', 'P'])?, exponent_bits)))
        .filter(|((_, precision), exponent_bits)| digits(precision) && digits(exponent_bits));
    match explicit {
        Some(((body, precision), exponent_bits)) => (
            body,
            FloatFormat::new(
                precision.parse().expect("decimal digits"),
                exponent_bits.parse().expect("decimal digits"),
            ),
        ),
        None => match token.strip_suffix(['f', 'F']) {
            Some(body) => (body, Some(FloatFormat::of(24, 8))),
            None => (
                token.strip_suffix(['d', 'D']).unwrap_or(token),
                Some(FloatFormat::of(53, 11)),
            ),
        },
    }
}

/// Whether `token` is in the lexical syntax of the `Float` sort (`domains.md`, FLOAT-SYNTAX):
/// `[+-]?[0-9]+(.[0-9]*)?` or `.[0-9]+` with an optional exponent, `[+-]?Infinity`, or `NaN`,
/// each with an optional `f`/`d` or `p<digits>x<digits>` suffix. A Float domain value denotes the
/// element its string names in that syntax, so a string outside it (`inf`, `-.5`, ` 1.0`) names
/// none, although general float parsers accept such spellings.
pub fn is_float_syntax(token: &str) -> bool {
    let digits = |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
    let body = match token
        .rsplit_once(['x', 'X'])
        .and_then(|(rest, exponent_bits)| Some((rest.rsplit_once(['p', 'P'])?, exponent_bits)))
    {
        Some(((body, precision), exponent_bits)) if digits(precision) && digits(exponent_bits) => {
            body
        }
        _ => token.strip_suffix(['f', 'F', 'd', 'D']).unwrap_or(token),
    };
    if body == "NaN" || body.strip_prefix(['+', '-']).unwrap_or(body) == "Infinity" {
        return true;
    }
    let (mantissa, exponent) = match body.split_once(['e', 'E']) {
        Some((mantissa, exponent)) => (mantissa, Some(exponent)),
        None => (body, None),
    };
    let exponent_ok = exponent
        .is_none_or(|exponent| digits(exponent.strip_prefix(['+', '-']).unwrap_or(exponent)));
    let mantissa_ok = match mantissa.strip_prefix('.') {
        Some(fraction) => digits(fraction),
        None => {
            let unsigned = mantissa.strip_prefix(['+', '-']).unwrap_or(mantissa);
            match unsigned.split_once('.') {
                Some((whole, fraction)) => {
                    digits(whole) && (fraction.is_empty() || digits(fraction))
                }
                None => digits(unsigned),
            }
        }
    };
    mantissa_ok && exponent_ok
}

/// The binary32 value of `text`, the body of a Float literal (without its suffix): Rust's
/// correctly rounded parse, and the infinities and NaN by name.
pub fn parse_f32(text: &str) -> Option<f32> {
    match text {
        "Infinity" => Some(f32::INFINITY),
        "-Infinity" => Some(f32::NEG_INFINITY),
        "NaN" => Some(f32::NAN),
        _ => text.parse().ok(),
    }
}

/// The binary64 value of `text`, as [`parse_f32`] reads binary32.
pub fn parse_f64(text: &str) -> Option<f64> {
    match text {
        "Infinity" => Some(f64::INFINITY),
        "-Infinity" => Some(f64::NEG_INFINITY),
        "NaN" => Some(f64::NAN),
        _ => text.parse().ok(),
    }
}

/// The canonical text of the binary32 value `value` (`canonical_float_text`).
pub fn canonical_f32(value: f32) -> String {
    canonical(
        value.is_nan(),
        value.is_infinite(),
        value.is_sign_negative(),
        value == 0.0,
        (!value.is_nan() && !value.is_infinite() && value != 0.0).then(|| format!("{value:.8e}")),
        24,
        8,
    )
}

/// The canonical text of the binary64 value `value` (`canonical_float_text`).
pub fn canonical_f64(value: f64) -> String {
    canonical(
        value.is_nan(),
        value.is_infinite(),
        value.is_sign_negative(),
        value == 0.0,
        (!value.is_nan() && !value.is_infinite() && value != 0.0).then(|| format!("{value:.16e}")),
        53,
        11,
    )
}

fn canonical(
    is_nan: bool,
    is_infinite: bool,
    is_sign_negative: bool,
    is_zero: bool,
    finite: Option<String>,
    precision: u32,
    exponent_bits: u32,
) -> String {
    let value = if is_nan {
        "NaN".into()
    } else if is_infinite {
        if is_sign_negative {
            "-Infinity"
        } else {
            "Infinity"
        }
        .into()
    } else if is_zero {
        if is_sign_negative { "-0e+00" } else { "0e+00" }.into()
    } else {
        normalize_exponent(finite.expect("finite nonzero Floats have decimal text"))
    };
    format!("{value}p{precision}x{exponent_bits}")
}

fn normalize_exponent(scientific: String) -> String {
    let (mantissa, exponent) = scientific
        .split_once('e')
        .expect("Rust scientific Float formatting includes an exponent");
    let exponent = exponent
        .parse::<i32>()
        .expect("Rust scientific Float formatting uses a decimal exponent");
    format!("{mantissa}e{exponent:+03}")
}
