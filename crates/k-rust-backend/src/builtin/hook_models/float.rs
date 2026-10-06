//! `FLOAT` against exact rational arithmetic rounded to binary32 and binary64.
//!
//! The model never uses the platform's floating-point operations: a value is decoded from its
//! bit pattern into `±n·2^e`, an operation is computed exactly on those integers, and the exact
//! result is rounded to nearest, ties to even, with the format's precision and exponent range
//! (`round`). Token syntax is read by a parser of the `FLOAT-SYNTAX` regular expressions that
//! computes the decimal's exact value, so the hooks' parsing and printing are checked too: every
//! result token must be in the syntax, and must denote the result.

use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use k_rust_kore::names::BuiltinSort;

use super::{Case, Draw, Env, Spec, Val, assert_reached, run};
use crate::term::{Sort, Term};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::builtin) enum Format {
    Binary32,
    Binary64,
}

impl Format {
    fn of(precision: &BigInt, exponent_bits: &BigInt) -> Option<Self> {
        match (precision.to_u32()?, exponent_bits.to_u32()?) {
            (24, 8) => Some(Self::Binary32),
            (53, 11) => Some(Self::Binary64),
            _ => None,
        }
    }

    fn precision(self) -> i64 {
        match self {
            Self::Binary32 => 24,
            Self::Binary64 => 53,
        }
    }

    fn exponent_bits(self) -> i64 {
        match self {
            Self::Binary32 => 8,
            Self::Binary64 => 11,
        }
    }

    fn emax(self) -> i64 {
        (1 << (self.exponent_bits() - 1)) - 1
    }

    fn emin(self) -> i64 {
        1 - self.emax()
    }

    fn fraction_bits(self) -> i64 {
        self.precision() - 1
    }

    fn sign_bit(self) -> u64 {
        1 << (self.fraction_bits() + self.exponent_bits())
    }

    fn infinity(self) -> u64 {
        ((1 << self.exponent_bits()) - 1) << self.fraction_bits()
    }

    fn nan(self) -> u64 {
        self.infinity() | 1 << (self.fraction_bits() - 1)
    }
}

/// The value of a bit pattern: `Finite(negative, n, e)` is `±n·2^e`.
#[derive(Clone, Debug)]
enum Exact {
    Nan,
    Infinite(bool),
    Finite(bool, BigUint, i64),
}

fn classify(format: Format, bits: u64) -> Exact {
    let negative = bits & format.sign_bit() != 0;
    let fraction = bits & ((1 << format.fraction_bits()) - 1);
    let field = (bits >> format.fraction_bits()) & ((1 << format.exponent_bits()) - 1);
    if field == (1 << format.exponent_bits()) - 1 {
        return if fraction == 0 {
            Exact::Infinite(negative)
        } else {
            Exact::Nan
        };
    }
    if field == 0 {
        return Exact::Finite(
            negative,
            BigUint::from(fraction),
            format.emin() - format.fraction_bits(),
        );
    }
    Exact::Finite(
        negative,
        BigUint::from(fraction | 1 << format.fraction_bits()),
        field as i64 - format.emax() - format.fraction_bits(),
    )
}

/// Every NaN as the one NaN a token denotes.
fn canonical(format: Format, bits: u64) -> u64 {
    if matches!(classify(format, bits), Exact::Nan) {
        format.nan()
    } else {
        bits
    }
}

fn float(format: Format, bits: u64) -> Val {
    Val::Float(format, canonical(format, bits))
}

fn signed_zero(format: Format, negative: bool) -> u64 {
    if negative { format.sign_bit() } else { 0 }
}

fn signed_infinity(format: Format, negative: bool) -> u64 {
    signed_zero(format, negative) | format.infinity()
}

/// `num/den ≥ 2^power`.
fn at_least_power(num: &BigUint, den: &BigUint, power: i64) -> bool {
    if power >= 0 {
        *num >= den << power
    } else {
        num << -power >= *den
    }
}

/// `±num/den` rounded to nearest, ties to even, in `format`, overflowing to infinity.
fn round(format: Format, negative: bool, num: &BigUint, den: &BigUint) -> u64 {
    let sign = signed_zero(format, negative);
    if num.is_zero() {
        return sign;
    }
    let precision = format.precision();
    let mut exponent = num.bits() as i64 - den.bits() as i64;
    if !at_least_power(num, den, exponent) {
        exponent -= 1;
    }
    let mut quantum = exponent.max(format.emin()) - (precision - 1);
    let (scaled_num, scaled_den) = if quantum <= 0 {
        (num << -quantum, den.clone())
    } else {
        (num.clone(), den << quantum)
    };
    let mut mantissa = &scaled_num / &scaled_den;
    let twice_remainder = (&scaled_num % &scaled_den) << 1;
    if twice_remainder > scaled_den || (twice_remainder == scaled_den && mantissa.bit(0)) {
        mantissa += 1_u8;
    }
    if mantissa.bits() as i64 > precision {
        mantissa >>= 1;
        quantum += 1;
    }
    let mantissa = mantissa.to_u64().expect("at most 53 bits");
    let hidden = 1_u64 << (precision - 1);
    if mantissa < hidden {
        return sign | mantissa;
    }
    let exponent = quantum + precision - 1;
    if exponent > format.emax() {
        return sign | format.infinity();
    }
    sign | ((exponent + format.emax()) as u64) << format.fraction_bits() | (mantissa - hidden)
}

/// `±n·2^e` rounded.
fn round_scaled(format: Format, negative: bool, n: &BigUint, e: i64) -> u64 {
    if e >= 0 {
        round(format, negative, &(n << e), &BigUint::one())
    } else {
        round(format, negative, n, &(BigUint::one() << -e))
    }
}

/// The signed integers `a·2^(ea - e)` and `b·2^(eb - e)` at the common exponent `e`.
fn aligned(
    (a_negative, a, ea): (bool, &BigUint, i64),
    (b_negative, b, eb): (bool, &BigUint, i64),
) -> (BigInt, BigInt, i64) {
    let e = ea.min(eb);
    let signed = |negative: bool, n: &BigUint, shift: i64| {
        let value = BigInt::from(n << shift);
        if negative { -value } else { value }
    };
    (
        signed(a_negative, a, ea - e),
        signed(b_negative, b, eb - e),
        e,
    )
}

fn add(format: Format, left: u64, right: u64) -> u64 {
    match (classify(format, left), classify(format, right)) {
        (Exact::Nan, _) | (_, Exact::Nan) => format.nan(),
        (Exact::Infinite(a), Exact::Infinite(b)) if a != b => format.nan(),
        (Exact::Infinite(negative), _) | (_, Exact::Infinite(negative)) => {
            signed_infinity(format, negative)
        }
        (Exact::Finite(a_negative, a, ea), Exact::Finite(b_negative, b, eb)) => {
            if a.is_zero() && b.is_zero() {
                return signed_zero(format, a_negative && b_negative);
            }
            let (a, b, e) = aligned((a_negative, &a, ea), (b_negative, &b, eb));
            let sum = a + b;
            // An exact zero sum of nonzero operands is +0 when rounding to nearest.
            round_scaled(format, sum.is_negative(), sum.magnitude(), e)
        }
    }
}

fn negate(format: Format, bits: u64) -> u64 {
    bits ^ format.sign_bit()
}

fn multiply(format: Format, left: u64, right: u64) -> u64 {
    let negative = (left ^ right) & format.sign_bit() != 0;
    match (classify(format, left), classify(format, right)) {
        (Exact::Nan, _) | (_, Exact::Nan) => format.nan(),
        (Exact::Infinite(_), Exact::Finite(_, n, _))
        | (Exact::Finite(_, n, _), Exact::Infinite(_))
            if n.is_zero() =>
        {
            format.nan()
        }
        (Exact::Infinite(_), _) | (_, Exact::Infinite(_)) => signed_infinity(format, negative),
        (Exact::Finite(_, a, ea), Exact::Finite(_, b, eb)) => {
            round_scaled(format, negative, &(a * b), ea + eb)
        }
    }
}

fn divide(format: Format, left: u64, right: u64) -> u64 {
    let negative = (left ^ right) & format.sign_bit() != 0;
    match (classify(format, left), classify(format, right)) {
        (Exact::Nan, _) | (_, Exact::Nan) | (Exact::Infinite(_), Exact::Infinite(_)) => {
            format.nan()
        }
        (Exact::Infinite(_), _) => signed_infinity(format, negative),
        (_, Exact::Infinite(_)) => signed_zero(format, negative),
        (Exact::Finite(_, a, _), Exact::Finite(_, b, _)) if b.is_zero() => {
            if a.is_zero() {
                format.nan()
            } else {
                signed_infinity(format, negative)
            }
        }
        (Exact::Finite(_, a, ea), Exact::Finite(_, b, eb)) => {
            let shift = ea - eb;
            if shift >= 0 {
                round(format, negative, &(a << shift), &b)
            } else {
                round(format, negative, &a, &(b << -shift))
            }
        }
    }
}

/// The order of two values, `None` when one is NaN; the zeros are equal.
fn compare(format: Format, left: u64, right: u64) -> Option<Ordering> {
    let rank = |exact: &Exact| match exact {
        Exact::Nan => None,
        Exact::Infinite(true) => Some(-1),
        Exact::Infinite(false) => Some(1),
        Exact::Finite(..) => Some(0),
    };
    let (left, right) = (classify(format, left), classify(format, right));
    match (rank(&left)?, rank(&right)?) {
        (0, 0) => {
            let (Exact::Finite(a_negative, a, ea), Exact::Finite(b_negative, b, eb)) =
                (left, right)
            else {
                unreachable!()
            };
            let (a, b, _) = aligned((a_negative, &a, ea), (b_negative, &b, eb));
            Some(a.cmp(&b))
        }
        (left, right) => Some(left.cmp(&right)),
    }
}

/// `floorFloat`, `ceilFloat` and `truncFloat`: the integer in the direction, keeping the sign of
/// a zero result.
fn integral(format: Format, bits: u64, direction: Ordering) -> u64 {
    let Exact::Finite(negative, n, e) = classify(format, bits) else {
        return canonical(format, bits);
    };
    if e >= 0 {
        return bits;
    }
    let mut magnitude = &n >> -e;
    let fractional = (&magnitude << -e) != n;
    // Away from zero: up for a positive value under ceil, down for a negative one under floor.
    let away = match direction {
        Ordering::Less => negative,
        Ordering::Greater => !negative,
        Ordering::Equal => false,
    };
    if fractional && away {
        magnitude += 1_u8;
    }
    round_scaled(format, negative, &magnitude, 0)
}

/// `rootFloat(x, 2)`: the Nth root of degree 2, which is IEEE 754 rootn(x, 2) and differs from
/// squareRoot only at -0, whose even root is +0.
fn square_root(format: Format, bits: u64) -> u64 {
    match classify(format, bits) {
        Exact::Nan | Exact::Infinite(true) => format.nan(),
        Exact::Infinite(false) => bits,
        Exact::Finite(_, n, _) if n.is_zero() => 0,
        Exact::Finite(true, ..) => format.nan(),
        Exact::Finite(false, mut n, mut e) => {
            if e.rem_euclid(2) == 1 {
                n <<= 1;
                e -= 1;
            }
            // sqrt(n·2^e) = sqrt(n·4^k)·2^(e/2 - k); with k = p + 3 the integer square root t
            // has more than p + 2 bits, so t + 1/2 rounds as the irrational root in (t, t + 1).
            let k = format.precision() + 3;
            let scaled = n << (2 * k);
            let root = scaled.sqrt();
            let quantum = e / 2 - k;
            if &root * &root == scaled {
                round_scaled(format, false, &root, quantum)
            } else {
                round_scaled(format, false, &((root << 1) + 1_u8), quantum - 1)
            }
        }
    }
}

fn convert(from: Format, to: Format, bits: u64) -> u64 {
    match classify(from, bits) {
        Exact::Nan => to.nan(),
        Exact::Infinite(negative) => signed_infinity(to, negative),
        Exact::Finite(negative, n, e) => round_scaled(to, negative, &n, e),
    }
}

fn from_integer(format: Format, value: &BigInt) -> u64 {
    round_scaled(format, value.is_negative(), value.magnitude(), 0)
}

/// The nearest integer, ties to even, or `None` for NaN and the infinities.
fn to_integer(format: Format, bits: u64) -> Option<BigInt> {
    let Exact::Finite(negative, n, e) = classify(format, bits) else {
        return None;
    };
    let magnitude = if e >= 0 {
        n << e
    } else {
        let quotient = &n >> -e;
        let twice_remainder = (&n - (&quotient << -e)) << 1;
        let unit = BigUint::one() << -e;
        if twice_remainder > unit || (twice_remainder == unit && quotient.bit(0)) {
            quotient + 1_u8
        } else {
            quotient
        }
    };
    let value = BigInt::from(magnitude);
    Some(if negative { -value } else { value })
}

fn maximum_value(format: Format) -> u64 {
    let precision = format.precision();
    round_scaled(
        format,
        false,
        &((BigUint::one() << precision) - 1_u8),
        format.emax() - precision + 1,
    )
}

// ---------------------------------------------------------------------------------------------
// Tokens.

/// The format and canonical bit pattern a token in `FLOAT-SYNTAX` denotes, or `None` when the
/// text is not in the syntax (or names a format the model does not cover).
pub(in crate::builtin) fn parse_token(token: &str) -> Option<(Format, u64)> {
    let digits = |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
    let (body, format) = if let Some((rest, exponent_bits)) = token.rsplit_once(['x', 'X'])
        && let Some((body, precision)) = rest.rsplit_once(['p', 'P'])
    {
        if !digits(precision) || !digits(exponent_bits) {
            return None;
        }
        (
            body,
            Format::of(&precision.parse().ok()?, &exponent_bits.parse().ok()?)?,
        )
    } else if let Some(body) = token.strip_suffix(['f', 'F']) {
        (body, Format::Binary32)
    } else if let Some(body) = token.strip_suffix(['d', 'D']) {
        (body, Format::Binary64)
    } else {
        (token, Format::Binary64)
    };
    let (negative, unsigned) = match body.as_bytes().first() {
        Some(b'-') => (true, &body[1..]),
        Some(b'+') => (false, &body[1..]),
        _ => (false, body),
    };
    if body == "NaN" {
        return Some((format, format.nan()));
    }
    if unsigned == "Infinity" {
        return Some((format, signed_infinity(format, negative)));
    }
    let (mantissa, exponent) = match unsigned.split_once(['e', 'E']) {
        Some((mantissa, exponent)) => {
            let unsigned_exponent = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
            if !digits(unsigned_exponent) {
                return None;
            }
            (mantissa, exponent.parse::<i64>().ok()?)
        }
        None => (unsigned, 0),
    };
    let (integer, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let integer_ok = digits(integer) || integer.is_empty();
    let fraction_ok = digits(fraction) || fraction.is_empty();
    // `[+-]?[0-9]+(\.[0-9]*)?` or `\.[0-9]+`: a mantissa without an integer part takes no sign.
    if !integer_ok
        || !fraction_ok
        || (integer.is_empty() && (fraction.is_empty() || unsigned.len() != body.len()))
    {
        return None;
    }
    let significand: BigUint = format!("{integer}{fraction}").parse().ok()?;
    let power = exponent - fraction.len() as i64;
    let ten = BigUint::from(10_u8);
    let bits = if power >= 0 {
        round(
            format,
            negative,
            &(significand * ten.pow(power as u32)),
            &BigUint::one(),
        )
    } else {
        round(format, negative, &significand, &ten.pow((-power) as u32))
    };
    Some((format, bits))
}

fn suffix(format: Format) -> &'static str {
    match format {
        Format::Binary32 => "f",
        Format::Binary64 => "",
    }
}

fn host_value(format: Format, bits: u64) -> f64 {
    match format {
        Format::Binary32 => f64::from(f32::from_bits(bits as u32)),
        Format::Binary64 => f64::from_bits(bits),
    }
}

/// Text of a value in the shortest-digits scientific form (exact for both formats; only the
/// generator and `encode` use the host's printing).
fn scientific(format: Format, bits: u64) -> String {
    match format {
        Format::Binary32 => format!("{:e}", f32::from_bits(bits as u32)),
        Format::Binary64 => format!("{:e}", f64::from_bits(bits)),
    }
}

pub(in crate::builtin) fn token_term(format: Format, bits: u64) -> Term {
    let text = match classify(format, bits) {
        Exact::Nan => "NaN".to_owned(),
        Exact::Infinite(negative) => if negative { "-Infinity" } else { "Infinity" }.to_owned(),
        Exact::Finite(..) => scientific(format, bits),
    };
    float_term(format!("{text}{}", suffix(format)))
}

fn float_term(text: String) -> Term {
    Term::domain_value(Sort::builtin(BuiltinSort::Float), text)
}

// ---------------------------------------------------------------------------------------------
// Cases.

const FLOAT_HOOKS: [&str; 25] = [
    "FLOAT.precision",
    "FLOAT.exponentBits",
    "FLOAT.sign",
    "FLOAT.isNaN",
    "FLOAT.neg",
    "FLOAT.abs",
    "FLOAT.floor",
    "FLOAT.ceil",
    "FLOAT.trunc",
    "FLOAT.root",
    "FLOAT.add",
    "FLOAT.sub",
    "FLOAT.mul",
    "FLOAT.div",
    "FLOAT.min",
    "FLOAT.max",
    "FLOAT.lt",
    "FLOAT.le",
    "FLOAT.gt",
    "FLOAT.ge",
    "FLOAT.eq",
    "FLOAT.round",
    "FLOAT.int2float",
    "FLOAT.float2int",
    "FLOAT.maxValue",
];

/// Interesting binary64 values; binary32 cases round them first.
const SPECIAL: [f64; 26] = [
    0.0,
    -0.0,
    f64::INFINITY,
    f64::NEG_INFINITY,
    f64::NAN,
    1.0,
    -1.0,
    0.5,
    -0.5,
    1.5,
    2.5,
    -2.5,
    3.0,
    0.1,
    0.49999999999999994,
    f64::MAX,
    f64::MIN_POSITIVE,
    5e-324,
    -5e-324,
    9007199254740991.0,
    9007199254740992.0,
    16777217.0,
    3.4028235677973366e38,
    1.401298464324817e-45,
    1e300,
    -7.0,
];

fn value_bits(draw: &mut Draw<'_>, format: Format) -> u64 {
    let host = match draw.below(4) {
        0 => {
            let bits = draw.u64();
            return match format {
                Format::Binary32 => bits & 0xffff_ffff,
                Format::Binary64 => bits,
            };
        }
        1 => {
            // A small dyadic rational, so that sums and products are often exact.
            let mantissa = draw.below(2001) as f64 - 1000.0;
            mantissa * 2_f64.powi(draw.below(21) as i32 - 10)
        }
        _ => draw.pick(&SPECIAL),
    };
    match format {
        Format::Binary32 => u64::from((host as f32).to_bits()),
        Format::Binary64 => host.to_bits(),
    }
}

/// A token for a value of `format`: its shortest form, a shortened decimal (which denotes a
/// nearby value), or the host's positional form, with a sign, exponent and suffix spelling
/// chosen at random.
fn token(draw: &mut Draw<'_>, format: Format, bits: u64) -> Term {
    let suffix = match format {
        Format::Binary32 => draw.pick(&["f", "F", "p24x8", "P24X8"]),
        Format::Binary64 => draw.pick(&["", "d", "D", "p53x11", "P53x11"]),
    };
    let text = match classify(format, bits) {
        Exact::Nan => "NaN".to_owned(),
        Exact::Infinite(negative) => {
            let sign = if negative { "-" } else { draw.pick(&["", "+"]) };
            format!("{sign}Infinity")
        }
        Exact::Finite(..) => {
            let value = host_value(format, bits);
            let text = match draw.below(5) {
                0 => format!("{:.*e}", draw.below(20), value),
                1 if value.abs() < 1e30 => format!("{value}"),
                2 => {
                    // `.5`, `5.`, `5.e1`, `+5E-1`: the corners of the mantissa syntax.
                    let digits = draw.below(1000);
                    let exponent = draw.below(9) as i64 - 4;
                    let shape = draw.below(4);
                    let sign = draw.pick(&["", "-", "+"]);
                    match shape {
                        // A mantissa without an integer part takes no sign.
                        0 => format!(".{digits}"),
                        1 => format!("{sign}{digits}."),
                        2 => format!("{sign}{digits}.e{exponent}"),
                        _ => format!("{sign}{digits}E{exponent:+}"),
                    }
                }
                _ => scientific(format, bits),
            };
            if draw.chance(1) && !text.starts_with(['-', '+', '.']) {
                format!("+{text}")
            } else {
                text
            }
        }
    };
    float_term(format!("{text}{suffix}"))
}

fn float_argument(draw: &mut Draw<'_>, env: &mut Env, format: Format) -> Term {
    let bits = value_bits(draw, format);
    let term = token(draw, format, bits);
    draw.scalar(term, Sort::builtin(BuiltinSort::Float), env)
}

fn format_arguments(draw: &mut Draw<'_>, env: &mut Env, format: Format) -> Vec<Term> {
    let (precision, exponent_bits) = match format {
        Format::Binary32 => (24, 8),
        Format::Binary64 => (53, 11),
    };
    vec![draw.int(precision, env), draw.int(exponent_bits, env)]
}

fn integer(draw: &mut Draw<'_>) -> BigInt {
    let one = BigInt::one;
    let magnitude = match draw.below(8) {
        0 => BigInt::from(draw.u64()),
        1 => one() << 24 | BigInt::from(draw.below(4)),
        2 => one() << 53 | BigInt::from(draw.below(4)),
        // Rounds through a tie only when the conversion keeps a sticky bit.
        3 => one() << 60 | one() << 36 | BigInt::from(draw.below(2)),
        4 => (one() << 1024) - (one() << 970) - BigInt::from(draw.below(2)),
        5 => (one() << 128) - (one() << 103) - BigInt::from(draw.below(2)),
        6 => BigInt::from(draw.u64()) << (64 + draw.below(1000)),
        _ => BigInt::from(draw.below(100)),
    };
    if draw.chance(3) {
        -magnitude
    } else {
        magnitude
    }
}

fn float_case(draw: &mut Draw<'_>) -> Case {
    let hook = draw.pick(&FLOAT_HOOKS);
    let format = draw.pick(&[Format::Binary32, Format::Binary64]);
    let mut env = Env::new();
    let env = &mut env;
    let arguments = match hook {
        "FLOAT.root" => {
            let degree = if draw.chance(1) { 3 } else { 2 };
            vec![float_argument(draw, env, format), draw.int(degree, env)]
        }
        "FLOAT.add" | "FLOAT.sub" | "FLOAT.mul" | "FLOAT.div" | "FLOAT.min" | "FLOAT.max"
        | "FLOAT.lt" | "FLOAT.le" | "FLOAT.gt" | "FLOAT.ge" | "FLOAT.eq" => {
            let left = value_bits(draw, format);
            let right = match draw.below(4) {
                0 => left,
                1 => negate(format, left),
                _ => value_bits(draw, format),
            };
            let left = token(draw, format, left);
            let right = token(draw, format, right);
            vec![
                draw.scalar(left, Sort::builtin(BuiltinSort::Float), env),
                draw.scalar(right, Sort::builtin(BuiltinSort::Float), env),
            ]
        }
        "FLOAT.round" => {
            let target = draw.pick(&[Format::Binary32, Format::Binary64]);
            let mut arguments = vec![float_argument(draw, env, format)];
            arguments.extend(format_arguments(draw, env, target));
            arguments
        }
        "FLOAT.int2float" => {
            let value = integer(draw);
            let mut arguments = vec![draw.int(value, env)];
            arguments.extend(format_arguments(draw, env, format));
            arguments
        }
        "FLOAT.maxValue" => format_arguments(draw, env, format),
        _ => vec![float_argument(draw, env, format)],
    };
    Case {
        hook,
        arguments,
        env: env.clone(),
    }
}

fn float_model(hook: &str, arguments: &[Val]) -> Spec {
    use Val::{Bool, Float, Int};
    let unary = |operation: &dyn Fn(Format, u64) -> u64| match arguments {
        [Float(format, bits)] => Spec::value(float(*format, operation(*format, *bits))),
        _ => panic!("{hook} takes one Float: {arguments:?}"),
    };
    let binary = |operation: &dyn Fn(Format, u64, u64) -> u64| match arguments {
        [Float(format, left), Float(right_format, right)] if format == right_format => {
            Spec::value(float(*format, operation(*format, *left, *right)))
        }
        _ => panic!("{hook} takes two Floats of one format: {arguments:?}"),
    };
    let comparison = |holds: &dyn Fn(Ordering) -> bool| match arguments {
        [Float(format, left), Float(_, right)] => {
            Spec::value(Bool(compare(*format, *left, *right).is_some_and(holds)))
        }
        _ => panic!("{hook} takes two Floats: {arguments:?}"),
    };
    // `fp.min` and `fp.max`: a NaN operand yields the other operand; the result for two zeros
    // of different signs is either zero.
    let extremum = |wanted: Ordering| match arguments {
        [Float(format, left), Float(_, right)] => {
            let (format, left, right) = (*format, *left, *right);
            match compare(format, left, right) {
                None if matches!(classify(format, left), Exact::Nan) => {
                    Spec::value(float(format, right))
                }
                None => Spec::value(float(format, left)),
                Some(Ordering::Equal) if left != right => Spec::one_of(vec![
                    float(format, signed_zero(format, false)),
                    float(format, signed_zero(format, true)),
                ]),
                Some(order) if order == wanted => Spec::value(float(format, left)),
                Some(_) => Spec::value(float(format, right)),
            }
        }
        _ => panic!("{hook} takes two Floats: {arguments:?}"),
    };
    match hook {
        "FLOAT.precision" | "FLOAT.exponentBits" => {
            let [Float(format, _)] = arguments else {
                panic!("{hook} takes one Float")
            };
            Spec::value(Val::int(if hook == "FLOAT.precision" {
                format.precision()
            } else {
                format.exponent_bits()
            }))
        }
        "FLOAT.sign" => {
            let [Float(format, bits)] = arguments else {
                panic!("{hook} takes one Float")
            };
            Spec::value(Bool(bits & format.sign_bit() != 0))
        }
        "FLOAT.isNaN" => {
            let [Float(format, bits)] = arguments else {
                panic!("{hook} takes one Float")
            };
            Spec::value(Bool(matches!(classify(*format, *bits), Exact::Nan)))
        }
        "FLOAT.neg" => unary(&|format, bits| negate(format, bits)),
        "FLOAT.abs" => unary(&|format, bits| bits & !format.sign_bit()),
        "FLOAT.floor" => unary(&|format, bits| integral(format, bits, Ordering::Less)),
        "FLOAT.ceil" => unary(&|format, bits| integral(format, bits, Ordering::Greater)),
        "FLOAT.trunc" => unary(&|format, bits| integral(format, bits, Ordering::Equal)),
        "FLOAT.root" => match arguments {
            [Float(format, bits), Int(degree)] if *degree == BigInt::from(2) => {
                Spec::value(float(*format, square_root(*format, *bits)))
            }
            // Other degrees are not modelled; the hook may decline them.
            _ => Spec::open(),
        },
        "FLOAT.add" => binary(&add),
        "FLOAT.sub" => binary(&|format, left, right| add(format, left, negate(format, right))),
        "FLOAT.mul" => binary(&multiply),
        "FLOAT.div" => binary(&divide),
        "FLOAT.min" => extremum(Ordering::Less),
        "FLOAT.max" => extremum(Ordering::Greater),
        "FLOAT.lt" => comparison(&|order| order == Ordering::Less),
        "FLOAT.le" => comparison(&|order| order != Ordering::Greater),
        "FLOAT.gt" => comparison(&|order| order == Ordering::Greater),
        "FLOAT.ge" => comparison(&|order| order != Ordering::Less),
        "FLOAT.eq" => comparison(&|order| order == Ordering::Equal),
        "FLOAT.round" => {
            let [Float(from, bits), Int(precision), Int(exponent_bits)] = arguments else {
                panic!("{hook} takes a Float and a format")
            };
            let to = Format::of(precision, exponent_bits).expect("a generated format");
            Spec::value(float(to, convert(*from, to, *bits)))
        }
        "FLOAT.int2float" => {
            let [Int(value), Int(precision), Int(exponent_bits)] = arguments else {
                panic!("{hook} takes an Int and a format")
            };
            let format = Format::of(precision, exponent_bits).expect("a generated format");
            Spec::value(float(format, from_integer(format, value)))
        }
        // `Float2Int` is declared total, but no integer is the nearest to NaN or an infinity;
        // the documentation does not say which value those get.
        "FLOAT.float2int" => {
            let [Float(format, bits)] = arguments else {
                panic!("{hook} takes one Float")
            };
            // Total, and NaN and the infinities have no nearest integer: unspecified there.
            to_integer(*format, *bits)
                .map_or_else(Spec::unspecified, |value| Spec::value(Int(value)))
        }
        "FLOAT.maxValue" => {
            let [Int(precision), Int(exponent_bits)] = arguments else {
                panic!("{hook} takes a format")
            };
            let format = Format::of(precision, exponent_bits).expect("a generated format");
            Spec::value(float(format, maximum_value(format)))
        }
        _ => panic!("no FLOAT model for {hook}"),
    }
}

#[test]
fn float_hooks_agree_with_an_exact_rounding_model() {
    let tallies = run(4000, &float_case, &float_model);
    assert_reached(&tallies, &FLOAT_HOOKS, &[]);
}

/// The model's rounding and token parser reproduce known IEEE values, so that the model is not
/// merely consistent with itself.
#[test]
fn the_float_model_reproduces_known_ieee_values() {
    let binary64 = |text: &str| parse_token(text).map(|(_, bits)| bits);
    assert_eq!(binary64("0.1"), Some(0.1_f64.to_bits()));
    assert_eq!(binary64("-0.0"), Some((-0.0_f64).to_bits()));
    assert_eq!(binary64("1e400"), Some(f64::INFINITY.to_bits()));
    assert_eq!(
        binary64("2.4703282292062328e-324"),
        Some(5e-324_f64.to_bits())
    );
    assert_eq!(binary64("2.4703282292062327e-324"), Some(0));
    assert_eq!(
        binary64("9007199254740993"),
        Some(9007199254740992_f64.to_bits())
    );
    assert_eq!(binary64(".5"), Some(0.5_f64.to_bits()));
    assert_eq!(binary64("-.5"), None);
    assert_eq!(binary64("+.5"), None);
    assert_eq!(binary64("5."), Some(5_f64.to_bits()));
    assert_eq!(binary64("1.0 "), None);
    assert_eq!(binary64("inf"), None);
    assert_eq!(binary64("1e"), None);
    assert_eq!(binary64("."), None);
    assert_eq!(
        parse_token("16777217f"),
        Some((Format::Binary32, u64::from(16777216_f32.to_bits())))
    );
    // The midpoint between the largest binary32 value and 2^128 rounds to even, which
    // overflows; just below it, the largest value.
    assert_eq!(
        parse_token("340282356779733661637539395458142568448f"),
        Some((Format::Binary32, Format::Binary32.infinity()))
    );
    assert_eq!(
        parse_token("340282356779733661637539395458142568447f"),
        Some((Format::Binary32, u64::from(f32::MAX.to_bits())))
    );
    assert_eq!(maximum_value(Format::Binary64), f64::MAX.to_bits());
    assert_eq!(
        maximum_value(Format::Binary32),
        u64::from(f32::MAX.to_bits())
    );
    assert_eq!(
        square_root(Format::Binary64, 2_f64.to_bits()),
        std::f64::consts::SQRT_2.to_bits()
    );
    assert_eq!(
        add(Format::Binary64, 0.1_f64.to_bits(), 0.2_f64.to_bits()),
        0.30000000000000004_f64.to_bits()
    );
    assert_eq!(
        from_integer(
            Format::Binary32,
            &((BigInt::one() << 60) + (BigInt::one() << 36) + 1)
        ),
        u64::from((((1_u64 << 60) + (1 << 37)) as f32).to_bits())
    );
    assert_eq!(
        to_integer(Format::Binary64, 2.5_f64.to_bits()),
        Some(BigInt::from(2))
    );
    assert_eq!(
        to_integer(Format::Binary64, (-3.5_f64).to_bits()),
        Some(BigInt::from(-4))
    );
}
