//! Portable IEEE binary32/binary64 implementations of K's `FLOAT` hooks.

use num_bigint::BigInt;

use super::{BuiltinError, BuiltinResult, bool_term, expect_arity, int_term};
use crate::term::{Sort, Term, TermKind};

#[derive(Clone, Copy, Debug)]
enum KFloat {
    Binary32(f32),
    Binary64(f64),
}

impl KFloat {
    fn parse(hook: &str, token: &str) -> Result<Self, BuiltinError> {
        let (text, precision, exponent_bits) = parse_parts(hook, token)?;
        match (precision, exponent_bits) {
            (24, 8) => parse_f32(text)
                .map(Self::Binary32)
                .ok_or_else(|| invalid_token(hook, token)),
            (53, 11) => parse_f64(text)
                .map(Self::Binary64)
                .ok_or_else(|| invalid_token(hook, token)),
            _ => Err(BuiltinError::UnsupportedFloatFormat {
                hook: hook.into(),
                precision,
                exponent_bits,
            }),
        }
    }

    fn precision(self) -> u32 {
        match self {
            Self::Binary32(_) => 24,
            Self::Binary64(_) => 53,
        }
    }

    fn exponent_bits(self) -> u32 {
        match self {
            Self::Binary32(_) => 8,
            Self::Binary64(_) => 11,
        }
    }

    fn is_sign_negative(self) -> bool {
        match self {
            Self::Binary32(value) => value.is_sign_negative(),
            Self::Binary64(value) => value.is_sign_negative(),
        }
    }

    fn is_nan(self) -> bool {
        match self {
            Self::Binary32(value) => value.is_nan(),
            Self::Binary64(value) => value.is_nan(),
        }
    }

    fn neg(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(-value),
            Self::Binary64(value) => Self::Binary64(-value),
        }
    }

    fn token(self) -> String {
        match self {
            Self::Binary32(value) => canonical_f32(value),
            Self::Binary64(value) => canonical_f64(value),
        }
    }
}

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    match hook {
        "FLOAT.precision" => inspect(hook, arguments, |value| {
            int_term(BigInt::from(value.precision()))
        }),
        "FLOAT.exponentBits" => inspect(hook, arguments, |value| {
            int_term(BigInt::from(value.exponent_bits()))
        }),
        "FLOAT.sign" => inspect(hook, arguments, |value| bool_term(value.is_sign_negative())),
        "FLOAT.isNaN" => inspect(hook, arguments, |value| bool_term(value.is_nan())),
        "FLOAT.neg" => inspect(hook, arguments, |value| float_term(value.neg())),
        _ => Ok(BuiltinResult::NotApplicable),
    }
}

fn inspect(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(KFloat) -> Term,
) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 1)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(operation(value)))
}

fn read_float(hook: &str, term: &Term) -> Result<Option<KFloat>, BuiltinError> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return Ok(None);
    };
    if sort != &Sort::simple("SortFloat") {
        return Ok(None);
    }
    KFloat::parse(hook, value).map(Some)
}

fn float_term(value: KFloat) -> Term {
    Term::domain_value(Sort::simple("SortFloat"), value.token())
}

fn parse_parts<'a>(hook: &str, token: &'a str) -> Result<(&'a str, u32, u32), BuiltinError> {
    if let Some((value_and_precision, exponent)) = token.rsplit_once(['x', 'X'])
        && let Some((value, precision)) = value_and_precision.rsplit_once(['p', 'P'])
    {
        let precision = precision.parse().map_err(|_| invalid_token(hook, token))?;
        let exponent_bits = exponent.parse().map_err(|_| invalid_token(hook, token))?;
        return Ok((value, precision, exponent_bits));
    }
    if let Some(value) = token.strip_suffix(['f', 'F']) {
        Ok((value, 24, 8))
    } else {
        Ok((token.strip_suffix(['d', 'D']).unwrap_or(token), 53, 11))
    }
}

fn parse_f32(text: &str) -> Option<f32> {
    match text {
        "Infinity" => Some(f32::INFINITY),
        "-Infinity" => Some(f32::NEG_INFINITY),
        "NaN" => Some(f32::NAN),
        _ => text.parse().ok(),
    }
}

fn parse_f64(text: &str) -> Option<f64> {
    match text {
        "Infinity" => Some(f64::INFINITY),
        "-Infinity" => Some(f64::NEG_INFINITY),
        "NaN" => Some(f64::NAN),
        _ => text.parse().ok(),
    }
}

fn invalid_token(hook: &str, token: &str) -> BuiltinError {
    BuiltinError::InvalidFloatToken {
        hook: hook.into(),
        token: token.into(),
    }
}

fn canonical_f32(value: f32) -> String {
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

fn canonical_f64(value: f64) -> String {
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
