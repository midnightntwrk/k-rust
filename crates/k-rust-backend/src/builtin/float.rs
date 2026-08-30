//! Portable IEEE binary32/binary64 implementations of K's `FLOAT` hooks.

use num_bigint::BigInt;
use num_traits::{FromPrimitive, ToPrimitive};

use super::{BuiltinError, BuiltinResult, bool_term, expect_arity, int_term, read_int};
use crate::term::{Sort, Term, TermKind};

#[derive(Clone, Copy, Debug)]
enum KFloat {
    Binary32(f32),
    Binary64(f64),
}

#[derive(Clone, Copy)]
enum BinaryOperation {
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
}

#[derive(Clone, Copy)]
enum Comparison {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
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

    fn abs(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(value.abs()),
            Self::Binary64(value) => Self::Binary64(value.abs()),
        }
    }

    fn floor(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(value.floor()),
            Self::Binary64(value) => Self::Binary64(value.floor()),
        }
    }

    fn ceil(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(value.ceil()),
            Self::Binary64(value) => Self::Binary64(value.ceil()),
        }
    }

    fn trunc(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(value.trunc()),
            Self::Binary64(value) => Self::Binary64(value.trunc()),
        }
    }

    fn sqrt(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(value.sqrt()),
            Self::Binary64(value) => Self::Binary64(value.sqrt()),
        }
    }

    fn binary(
        self,
        other: Self,
        hook: &str,
        operation: BinaryOperation,
    ) -> Result<Self, BuiltinError> {
        match (self, other) {
            (Self::Binary32(left), Self::Binary32(right)) => Ok(Self::Binary32(match operation {
                BinaryOperation::Add => left + right,
                BinaryOperation::Sub => left - right,
                BinaryOperation::Mul => left * right,
                BinaryOperation::Div => left / right,
                BinaryOperation::Min => minimum_f32(left, right),
                BinaryOperation::Max => maximum_f32(left, right),
            })),
            (Self::Binary64(left), Self::Binary64(right)) => Ok(Self::Binary64(match operation {
                BinaryOperation::Add => left + right,
                BinaryOperation::Sub => left - right,
                BinaryOperation::Mul => left * right,
                BinaryOperation::Div => left / right,
                BinaryOperation::Min => minimum_f64(left, right),
                BinaryOperation::Max => maximum_f64(left, right),
            })),
            (left, right) => Err(BuiltinError::MismatchedFloatFormats {
                hook: hook.into(),
                left_precision: left.precision(),
                left_exponent_bits: left.exponent_bits(),
                right_precision: right.precision(),
                right_exponent_bits: right.exponent_bits(),
            }),
        }
    }

    fn compare(self, other: Self, comparison: Comparison) -> bool {
        let left = self.as_f64();
        let right = other.as_f64();
        match comparison {
            Comparison::Less => left < right,
            Comparison::LessEqual => left <= right,
            Comparison::Greater => left > right,
            Comparison::GreaterEqual => left >= right,
            Comparison::Equal => left == right,
        }
    }

    fn as_f64(self) -> f64 {
        match self {
            Self::Binary32(value) => f64::from(value),
            Self::Binary64(value) => value,
        }
    }

    fn round_to(self, precision: u32, exponent_bits: u32) -> Self {
        match (precision, exponent_bits) {
            (24, 8) => Self::Binary32(match self {
                Self::Binary32(value) => value,
                Self::Binary64(value) => value as f32,
            }),
            (53, 11) => Self::Binary64(self.as_f64()),
            _ => unreachable!("the requested Float format was validated"),
        }
    }

    fn round_to_integer(self) -> Option<BigInt> {
        let rounded = match self {
            Self::Binary32(value) => f64::from(value.round_ties_even()),
            Self::Binary64(value) => value.round_ties_even(),
        };
        BigInt::from_f64(rounded)
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
        "FLOAT.abs" => inspect(hook, arguments, |value| float_term(value.abs())),
        "FLOAT.floor" => inspect(hook, arguments, |value| float_term(value.floor())),
        "FLOAT.ceil" => inspect(hook, arguments, |value| float_term(value.ceil())),
        "FLOAT.trunc" => inspect(hook, arguments, |value| float_term(value.trunc())),
        "FLOAT.root" => root(hook, arguments),
        "FLOAT.add" => binary(hook, arguments, BinaryOperation::Add),
        "FLOAT.sub" => binary(hook, arguments, BinaryOperation::Sub),
        "FLOAT.mul" => binary(hook, arguments, BinaryOperation::Mul),
        "FLOAT.div" => binary(hook, arguments, BinaryOperation::Div),
        "FLOAT.min" => binary(hook, arguments, BinaryOperation::Min),
        "FLOAT.max" => binary(hook, arguments, BinaryOperation::Max),
        "FLOAT.lt" => compare(hook, arguments, Comparison::Less),
        "FLOAT.le" => compare(hook, arguments, Comparison::LessEqual),
        "FLOAT.gt" => compare(hook, arguments, Comparison::Greater),
        "FLOAT.ge" => compare(hook, arguments, Comparison::GreaterEqual),
        "FLOAT.eq" => compare(hook, arguments, Comparison::Equal),
        "FLOAT.round" => round(hook, arguments),
        "FLOAT.int2float" => int_to_float(hook, arguments),
        "FLOAT.float2int" => float_to_int(hook, arguments),
        "FLOAT.maxValue" => maximum_value(hook, arguments),
        _ => Ok(BuiltinResult::NotApplicable),
    }
}

fn root(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(degree) = read_int(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    if degree != BigInt::from(2) {
        return Ok(BuiltinResult::NotApplicable);
    }
    Ok(BuiltinResult::Value(float_term(value.sqrt())))
}

fn round(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 3)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((precision, exponent_bits)) = read_format(hook, &arguments[1], &arguments[2])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(float_term(
        value.round_to(precision, exponent_bits),
    )))
}

fn int_to_float(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 3)?;
    let Some(integer) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((precision, exponent_bits)) = read_format(hook, &arguments[1], &arguments[2])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let value = match (precision, exponent_bits) {
        (24, 8) => KFloat::Binary32(
            integer
                .to_f32()
                .expect("num-bigint defines binary32 conversion for every BigInt"),
        ),
        (53, 11) => KFloat::Binary64(
            integer
                .to_f64()
                .expect("num-bigint defines binary64 conversion for every BigInt"),
        ),
        _ => unreachable!("the requested Float format was validated"),
    };
    Ok(BuiltinResult::Value(float_term(value)))
}

fn float_to_int(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 1)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(value
        .round_to_integer()
        .map(int_term)
        .map_or(BuiltinResult::Bottom, BuiltinResult::Value))
}

fn maximum_value(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let Some((precision, exponent_bits)) = read_format(hook, &arguments[0], &arguments[1])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let value = match (precision, exponent_bits) {
        (24, 8) => KFloat::Binary32(f32::MAX),
        (53, 11) => KFloat::Binary64(f64::MAX),
        _ => unreachable!("the requested Float format was validated"),
    };
    Ok(BuiltinResult::Value(float_term(value)))
}

fn read_format(
    hook: &str,
    precision: &Term,
    exponent_bits: &Term,
) -> Result<Option<(u32, u32)>, BuiltinError> {
    let Some(precision) = read_int(precision) else {
        return Ok(None);
    };
    let Some(exponent_bits) = read_int(exponent_bits) else {
        return Ok(None);
    };
    let (Some(precision_u32), Some(exponent_bits_u32)) =
        (precision.to_u32(), exponent_bits.to_u32())
    else {
        return Err(BuiltinError::UnsupportedFloatFormatParameters {
            hook: hook.into(),
            precision: precision.to_string(),
            exponent_bits: exponent_bits.to_string(),
        });
    };
    match (precision_u32, exponent_bits_u32) {
        (24, 8) | (53, 11) => Ok(Some((precision_u32, exponent_bits_u32))),
        _ => Err(BuiltinError::UnsupportedFloatFormat {
            hook: hook.into(),
            precision: precision_u32,
            exponent_bits: exponent_bits_u32,
        }),
    }
}

fn binary(
    hook: &str,
    arguments: &[Term],
    operation: BinaryOperation,
) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let Some(left) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(right) = read_float(hook, &arguments[1])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(float_term(
        left.binary(right, hook, operation)?,
    )))
}

fn compare(
    hook: &str,
    arguments: &[Term],
    comparison: Comparison,
) -> Result<BuiltinResult, BuiltinError> {
    expect_arity(hook, arguments, 2)?;
    let Some(left) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(right) = read_float(hook, &arguments[1])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(bool_term(
        left.compare(right, comparison),
    )))
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

fn minimum_f32(left: f32, right: f32) -> f32 {
    if left.is_nan() {
        right
    } else if right.is_nan() || left < right {
        left
    } else if right < left {
        right
    } else if left == 0.0 && (left.is_sign_negative() || right.is_sign_negative()) {
        -0.0
    } else {
        left
    }
}

fn maximum_f32(left: f32, right: f32) -> f32 {
    if left.is_nan() {
        right
    } else if right.is_nan() || left > right {
        left
    } else if right > left {
        right
    } else if left == 0.0 && (!left.is_sign_negative() || !right.is_sign_negative()) {
        0.0
    } else {
        left
    }
}

fn minimum_f64(left: f64, right: f64) -> f64 {
    if left.is_nan() {
        right
    } else if right.is_nan() || left < right {
        left
    } else if right < left {
        right
    } else if left == 0.0 && (left.is_sign_negative() || right.is_sign_negative()) {
        -0.0
    } else {
        left
    }
}

fn maximum_f64(left: f64, right: f64) -> f64 {
    if left.is_nan() {
        right
    } else if right.is_nan() || left > right {
        left
    } else if right > left {
        right
    } else if left == 0.0 && (!left.is_sign_negative() || !right.is_sign_negative()) {
        0.0
    } else {
        left
    }
}
