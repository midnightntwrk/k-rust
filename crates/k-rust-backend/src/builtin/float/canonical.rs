//! The canonical text of a `Float` domain value: one text per value, in every format.
//!
//! A Float literal's mantissa and exponent name a rational number, rounded to nearest, ties to
//! even, in the format its suffix names (`domains.md`, "Floating-point numbers"): no suffix, `d`
//! or `D` is binary64 (`p53x11`), `f` or `F` is binary32 (`p24x8`), and `pNxM` has `N` bits of
//! precision (the implicit bit included) and `M` exponent bits, represented like an IEEE 754
//! format: `emax = 2^(M-1) - 1`, `emin = 1 - emax`, with subnormals and overflow to the infinity
//! of the sign. The format is part of the value (`0.5f` and `0.5` are two values), the zeros of
//! the two signs are two values, and the literal syntax names one NaN per format.
//!
//! The canonical text of a value is:
//! - binary32 and binary64: the text the Float hooks write (`canonical_f32`, `canonical_f64`:
//!   `2.0000000000000000e+00p53x11`, `-0e+00p53x11`, `Infinityp53x11`, `NaNp24x8`), which
//!   round-trips; Rust's correctly rounded parse is the rounding;
//! - every other format: the exact decimal `[-]De<Q>p<N>x<M>` of the rounded value `D * 10^Q`,
//!   with `D` a decimal integer without trailing zeros, the zeros `0e0p<N>x<M>` and
//!   `-0e0p<N>x<M>`, the specials `Infinityp<N>x<M>`, `-Infinityp<N>x<M>` and `NaNp<N>x<M>`, and
//!   `N` and `M` in canonical decimal. Every binary value has a finite decimal expansion, so the
//!   text is exact, unique, and itself a literal of the value.
//!
//! A format whose precision or exponent-bits field is 0 names no format, so its literals name no
//! element. One whose field is 1 has no IEEE-like parameters (no trailing significand bit, or
//! `emin > emax`); k-rust does not compute it and refuses its literals as a bound of its own.
//!
//! The canonical text of a format other than binary32 and binary64 grows with the value's binary
//! exponent: a value `m * 2^e` with `e < 0` writes `D = m * 5^-e`, about `N + 2.32|e|` bits. The
//! text, and the exact arithmetic that finds it, are bounded by [`MAX_FLOAT_CANONICAL_BITS`],
//! estimated from the literal's digit count, its decimal exponent and the format before any
//! arithmetic beyond that size ([`float_canonical_bits_estimate`]); a literal beyond it is
//! refused (fail-closed), never read as another value.

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::{canonical_f32, canonical_f64, parse_f32, parse_f64};

/// The bound on the canonical text of a Float domain value of a format other than binary32 and
/// binary64: the bits of its decimal significand `D`, and of the exact arithmetic that rounds the
/// literal and writes `D`. 2^20 bits is 315,653 decimal digits.
pub const MAX_FLOAT_CANONICAL_BITS: u64 = 1 << 20;

/// Why a text has no canonical Float text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FloatTextRefusal {
    /// The text is outside the lexical syntax of `Float` (FLOAT-SYNTAX): it names no element.
    NotALiteral,
    /// A precision or exponent-bits field is 0: the suffix names no format, so the text names
    /// no element.
    ZeroFormatField,
    /// A precision or exponent-bits field is 1: a format without IEEE-like parameters, which
    /// k-rust does not compute. The text names a value of that format; k-rust declines it.
    UncomputedFormat,
    /// The canonical text, or the exact arithmetic that finds it, is estimated above
    /// [`MAX_FLOAT_CANONICAL_BITS`]. The text names a value; k-rust declines to write it.
    BeyondBound {
        /// The estimate, in bits (saturating).
        estimate_bits: u64,
    },
}

impl FloatTextRefusal {
    /// True when the text names no element of any Float format; false when it names a value k-rust
    /// declines to build (a format with a field of 1, or a text beyond the bound).
    pub fn names_no_element(self) -> bool {
        matches!(self, Self::NotALiteral | Self::ZeroFormatField)
    }
}

/// The canonical text of the Float value the literal `token` names, or why it has none.
///
/// `2.0`, `2.0d`, `0.2e1`, `2.0p53x11`, `2.0p053x011` and `2.00000000000000001` all give
/// `2.0000000000000000e+00p53x11`; `1.0p11x5` and `1.0001p11x5` both give `1e0p11x5`.
pub fn canonical_float_text(token: &str) -> Result<String, FloatTextRefusal> {
    match Literal::parse(token)? {
        Literal::Binary32(body) => parse_f32(body)
            .map(canonical_f32)
            .ok_or(FloatTextRefusal::NotALiteral),
        Literal::Binary64(body) => parse_f64(body)
            .map(canonical_f64)
            .ok_or(FloatTextRefusal::NotALiteral),
        Literal::Other(other) => other.plan()?.text(),
    }
}

/// An upper bound, in bits, on the canonical text of the Float literal `token` (its decimal
/// significand) and on the exact arithmetic that finds it, computed with no arithmetic on
/// numbers larger than [`MAX_FLOAT_CANONICAL_BITS`] bits. A literal whose estimate exceeds the
/// bound is refused (`BeyondBound`). binary32 and binary64 texts are at most 64 bits.
///
/// The frontend's constant fold uses it to leave unfolded a Float result whose canonical text
/// the backend would refuse.
pub fn float_canonical_bits_estimate(token: &str) -> Result<u64, FloatTextRefusal> {
    match Literal::parse(token)? {
        Literal::Binary32(_) | Literal::Binary64(_) => Ok(64),
        Literal::Other(other) => Ok(other.plan()?.estimate_bits),
    }
}

/// `log2(10)` and `log2(5)` bracketed by rationals over `10^9`: `LOW / 10^9 < log2 < HIGH / 10^9`.
const LOG2_10: (u64, u64) = (3_321_928_094, 3_321_928_095);
const LOG2_5: (u64, u64) = (2_321_928_094, 2_321_928_095);
const LOG_SCALE: u64 = 1_000_000_000;

/// A Float literal split into its body and its format.
enum Literal<'a> {
    Binary32(&'a str),
    Binary64(&'a str),
    Other(Other<'a>),
}

/// A literal of a format other than binary32 and binary64, both fields at least 2.
struct Other<'a> {
    negative: bool,
    magnitude: Magnitude,
    precision: BigUint,
    exponent_bits: BigUint,
    _body: &'a str,
}

/// The magnitude a literal's body names.
enum Magnitude {
    NaN,
    Infinity,
    Zero,
    /// `digits * 10^exponent`, `digits` a decimal integer without leading or trailing zeros.
    Finite {
        digits: String,
        exponent: BigInt,
    },
}

impl<'a> Literal<'a> {
    fn parse(token: &'a str) -> Result<Self, FloatTextRefusal> {
        if !super::is_float_syntax(token) {
            return Err(FloatTextRefusal::NotALiteral);
        }
        let digits =
            |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
        let explicit = token
            .rsplit_once(['x', 'X'])
            .and_then(|(rest, exponent_bits)| Some((rest.rsplit_once(['p', 'P'])?, exponent_bits)))
            .filter(|((_, precision), exponent_bits)| digits(precision) && digits(exponent_bits));
        let Some(((body, precision), exponent_bits)) = explicit else {
            return Ok(match token.strip_suffix(['f', 'F']) {
                Some(body) => Self::Binary32(body),
                None => Self::Binary64(token.strip_suffix(['d', 'D']).unwrap_or(token)),
            });
        };
        let precision: BigUint = precision.parse().expect("decimal digits");
        let exponent_bits: BigUint = exponent_bits.parse().expect("decimal digits");
        if precision.is_zero() || exponent_bits.is_zero() {
            return Err(FloatTextRefusal::ZeroFormatField);
        }
        if precision.is_one() || exponent_bits.is_one() {
            return Err(FloatTextRefusal::UncomputedFormat);
        }
        match (precision.to_u32(), exponent_bits.to_u32()) {
            (Some(24), Some(8)) => return Ok(Self::Binary32(body)),
            (Some(53), Some(11)) => return Ok(Self::Binary64(body)),
            _ => {}
        }
        let (negative, magnitude) = Magnitude::parse(body);
        Ok(Self::Other(Other {
            negative,
            magnitude,
            precision,
            exponent_bits,
            _body: body,
        }))
    }
}

impl Magnitude {
    /// The sign and magnitude of a body in FLOAT-SYNTAX (without its suffix).
    fn parse(body: &str) -> (bool, Self) {
        if body == "NaN" {
            return (false, Self::NaN);
        }
        let (negative, unsigned) = match body.as_bytes().first() {
            Some(b'-') => (true, &body[1..]),
            Some(b'+') => (false, &body[1..]),
            _ => (false, body),
        };
        if unsigned == "Infinity" {
            return (negative, Self::Infinity);
        }
        let (mantissa, exponent) = match unsigned.split_once(['e', 'E']) {
            Some((mantissa, exponent)) => (mantissa, Some(exponent)),
            None => (unsigned, None),
        };
        let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
        let mut exponent = exponent.map_or_else(BigInt::zero, |exponent| {
            let (sign, magnitude) = match exponent.as_bytes().first() {
                Some(b'-') => (Sign::Minus, &exponent[1..]),
                Some(b'+') => (Sign::Plus, &exponent[1..]),
                _ => (Sign::Plus, exponent),
            };
            BigInt::from_biguint(sign, magnitude.parse().expect("decimal digits"))
        });
        exponent -= fraction.len();
        let all = format!("{whole}{fraction}");
        let significant = all.trim_start_matches('0');
        let trimmed = significant.trim_end_matches('0');
        if trimmed.is_empty() {
            return (negative, Self::Zero);
        }
        exponent += significant.len() - trimmed.len();
        (
            negative,
            Self::Finite {
                digits: trimmed.to_owned(),
                exponent,
            },
        )
    }
}

/// The exponent range of a format: `Unbounded` when `emax` exceeds every exponent the value
/// could reach by more than its precision, so that neither overflow nor subnormals can occur and
/// `emax` (possibly `2^(2^40)`) is never materialized.
enum Range {
    Unbounded,
    Bounded { emax: BigInt, emin: BigInt },
}

/// What rounding a finite literal in its format leads to, with the estimate of its cost.
struct Plan<'a> {
    other: &'a Other<'a>,
    estimate_bits: u64,
    outcome: Outcome,
}

enum Outcome {
    /// The text is final: a special, a zero, or an overflow or underflow decided by exponent
    /// bounds alone.
    Text(String),
    /// The value is exactly representable: its exact decimal is the literal's own digits and
    /// exponent.
    Exact,
    /// The value is rounded to `precision` bits (at most the bound) in this range.
    Round {
        significand: BigUint,
        exponent: BigInt,
        precision: u64,
        range: Range,
    },
}

impl Other<'_> {
    fn suffix(&self) -> String {
        format!("p{}x{}", self.precision, self.exponent_bits)
    }

    fn signed(&self, text: &str) -> String {
        let sign = if self.negative { "-" } else { "" };
        format!("{sign}{text}{}", self.suffix())
    }

    fn plan(&self) -> Result<Plan<'_>, FloatTextRefusal> {
        let small = |outcome| {
            Ok(Plan {
                other: self,
                estimate_bits: 1,
                outcome,
            })
        };
        let (digits, exponent) = match &self.magnitude {
            Magnitude::NaN => return small(Outcome::Text(format!("NaN{}", self.suffix()))),
            Magnitude::Infinity => return small(Outcome::Text(self.signed("Infinity"))),
            Magnitude::Zero => return small(Outcome::Text(self.signed("0e0"))),
            Magnitude::Finite { digits, exponent } => (digits, exponent),
        };
        let precision = BigInt::from(self.precision.clone());
        // `10^(d10) <= v < 10^(d10 + 1)`, so `log2 v` lies in `[d10, d10 + 1) * log2(10)`.
        let d10 = exponent + (digits.len() - 1);
        let e2_low = scale_floor(&d10, LOG2_10) - 1;
        let e2_high = scale_ceil(&(&d10 + 1), LOG2_10);
        let range = self.range(&e2_low, &e2_high);
        if let Range::Bounded { emax, emin } = &range {
            // `v >= 2^(emax + 1)`, beyond the overflow threshold `2^(emax+1) - 2^(emax-N)`.
            if e2_low > *emax {
                return small(Outcome::Text(self.signed("Infinity")));
            }
            // `v < 2^(emin - N)`, below half the least subnormal `2^(emin - N + 1)`.
            if e2_high < emin - &precision {
                return small(Outcome::Text(self.signed("0e0")));
            }
        }
        let bound = BigInt::from(MAX_FLOAT_CANONICAL_BITS);
        let refuse = |estimate: &BigInt| FloatTextRefusal::BeyondBound {
            estimate_bits: estimate.to_u64().unwrap_or(u64::MAX),
        };
        // The literal's digits, below `10^L <= 2^B`.
        let digit_bits = scale_ceil(&BigInt::from(digits.len()), LOG2_10);
        if digit_bits > bound {
            return Err(refuse(&digit_bits));
        }
        // An exactly representable value is written with the literal's own digits; whether it
        // is one is decided on its binary form `odd * 2^shift`, computed within the bound.
        let mut work = digit_bits.clone();
        let mut exact_e2 = None;
        if let Some(dyadic_bits) = dyadic_bits(exponent, &digit_bits) {
            work = work.max(dyadic_bits);
            if work > bound {
                return Err(refuse(&work));
            }
            let value: BigUint = digits.parse().expect("decimal digits");
            if let Some((odd, shift)) = dyadic(value, exponent) {
                let bits = BigInt::from(odd.bits());
                let e2: BigInt = &shift + &bits - 1;
                // In range, and its lowest bit at or above the least subnormal's,
                // `2^(emin - N + 1)`.
                let fits = match &range {
                    Range::Unbounded => true,
                    Range::Bounded { emax, emin } => e2 <= *emax && shift > emin - &precision,
                };
                if bits <= precision && fits {
                    return Ok(Plan {
                        other: self,
                        estimate_bits: work.to_u64().expect("within the bound"),
                        outcome: Outcome::Exact,
                    });
                }
                exact_e2 = Some(e2);
            }
        }
        // Rounded to `N` bits with the quantum `2^u`, `u = max(e2, emin) - N + 1`: `D` has at
        // most `N + 2.33 * -u` bits for `u < 0` and `e2 + 2` for `u >= 0`; the exact quotient
        // works on `m * 10^max(q, 0) * 2^max(-u, 0)` and `10^max(-q, 0) * 2^max(u, 0)`.
        let (e2_low, e2_high) = match &exact_e2 {
            Some(e2) => (e2.clone(), e2.clone()),
            None => (e2_low, e2_high),
        };
        let floor_at = |e2: &BigInt| match &range {
            Range::Unbounded => e2.clone(),
            Range::Bounded { emin, .. } => e2.max(emin).clone(),
        };
        let quantum_low: BigInt = floor_at(&e2_low) - &precision + 1;
        let quantum_high: BigInt = floor_at(&e2_high) - &precision + 1;
        let zero = BigInt::zero();
        let significand_bits = if quantum_low.is_negative() {
            &precision + scale_ceil(&-&quantum_low, LOG2_5) + 1
        } else {
            zero.clone()
        }
        .max(if quantum_high.is_negative() {
            zero.clone()
        } else {
            &e2_high + 2
        });
        let numerator_bits = &digit_bits
            + scale_ceil(&exponent.max(&zero).clone(), LOG2_10)
            + (-&quantum_low).max(zero.clone())
            + 1;
        let denominator_bits =
            scale_ceil(&(-exponent).max(zero.clone()), LOG2_10) + quantum_high.max(zero) + 1;
        let estimate = work
            .max(significand_bits)
            .max(numerator_bits)
            .max(denominator_bits);
        if estimate > bound {
            return Err(refuse(&estimate));
        }
        Ok(Plan {
            other: self,
            estimate_bits: estimate.to_u64().expect("within the bound"),
            outcome: Outcome::Round {
                significand: digits.parse().expect("decimal digits"),
                exponent: exponent.clone(),
                precision: self.precision.to_u64().expect("within the bound"),
                range,
            },
        })
    }

    fn range(&self, e2_low: &BigInt, e2_high: &BigInt) -> Range {
        let reach = e2_low.bits().max(e2_high.bits()) + self.precision.bits() + 4;
        if self.exponent_bits > BigUint::from(reach) + 1_u8 {
            return Range::Unbounded;
        }
        let emax = (BigInt::one() << (self.exponent_bits.to_u64().expect("small") - 1)) - 1;
        let emin = 1 - &emax;
        Range::Bounded { emax, emin }
    }
}

impl Plan<'_> {
    fn text(self) -> Result<String, FloatTextRefusal> {
        let other = self.other;
        Ok(match self.outcome {
            Outcome::Text(text) => text,
            Outcome::Exact => {
                let Magnitude::Finite { digits, exponent } = &other.magnitude else {
                    unreachable!("an exact plan is of a finite literal")
                };
                other.signed(&format!("{digits}e{exponent}"))
            }
            Outcome::Round {
                significand,
                exponent,
                precision,
                range,
            } => match round(significand, &exponent, precision, &range) {
                Rounded::Zero => other.signed("0e0"),
                Rounded::Infinity => other.signed("Infinity"),
                Rounded::Finite(significand, quantum) => {
                    other.signed(&exact_decimal(significand, quantum))
                }
            },
        })
    }
}

/// The bits `5^|q|` (and `m * 5^q`) take when the value `m * 10^q` may be dyadic: always for
/// `q >= 0`, and for `q < 0` only when `5^|q|` can divide `m`, that is when `|q| * log2(5)` is
/// below the digits' bits `B`; `None` when it cannot be dyadic.
fn dyadic_bits(exponent: &BigInt, digit_bits: &BigInt) -> Option<BigInt> {
    if exponent.is_negative() {
        let five_bits = scale_floor(&-exponent, LOG2_5);
        (five_bits < *digit_bits).then(|| digit_bits.clone())
    } else {
        Some(digit_bits + scale_ceil(exponent, LOG2_5) + 1)
    }
}

/// `value * 10^exponent` as `odd * 2^shift` with `odd` odd, when it is dyadic.
fn dyadic(value: BigUint, exponent: &BigInt) -> Option<(BigUint, BigInt)> {
    let power = exponent.magnitude().to_u32().expect("within the bound");
    let fives = BigUint::from(5_u8).pow(power);
    let (whole, shift) = if exponent.is_negative() {
        let (quotient, remainder) = (&value / &fives, &value % &fives);
        if !remainder.is_zero() {
            return None;
        }
        (quotient, exponent.clone())
    } else {
        (value * fives, exponent.clone())
    };
    let zeros = whole.trailing_zeros().expect("a nonzero value");
    Some((whole >> zeros, shift + zeros))
}

enum Rounded {
    Zero,
    Infinity,
    /// `significand * 2^quantum`.
    Finite(BigUint, BigInt),
}

/// `digits * 10^exponent` rounded to nearest, ties to even, with `precision` significant bits in
/// `range`, with subnormals and overflow to infinity.
fn round(digits: BigUint, exponent: &BigInt, precision: u64, range: &Range) -> Rounded {
    let power = exponent.magnitude().to_u32().expect("within the bound");
    let tens = BigUint::from(10_u8).pow(power);
    let (mut numerator, mut denominator) = if exponent.is_negative() {
        (digits, tens)
    } else {
        (digits * tens, BigUint::one())
    };
    // `e2 = floor(log2(numerator / denominator))`.
    let mut e2 = numerator.bits() as i64 - denominator.bits() as i64;
    let at_least = |e2: i64| {
        if e2 >= 0 {
            numerator >= (&denominator << e2)
        } else {
            (&numerator << -e2) >= denominator
        }
    };
    if !at_least(e2) {
        e2 -= 1;
    }
    let precision = i64::try_from(precision).expect("within the bound");
    let floor = match range {
        Range::Unbounded => e2,
        Range::Bounded { emin, .. } => e2.max(emin.to_i64().unwrap_or(i64::MIN)),
    };
    let mut quantum = floor - precision + 1;
    if quantum <= 0 {
        numerator <<= -quantum;
    } else {
        denominator <<= quantum;
    }
    let mut significand = &numerator / &denominator;
    let twice_remainder = (&numerator % &denominator) << 1;
    if twice_remainder > denominator || (twice_remainder == denominator && significand.bit(0)) {
        significand += 1_u8;
    }
    if significand.bits() as i64 > precision {
        significand >>= 1;
        quantum += 1;
    }
    if significand.is_zero() {
        return Rounded::Zero;
    }
    if let Range::Bounded { emax, .. } = range
        && BigInt::from(quantum + significand.bits() as i64 - 1) > *emax
    {
        return Rounded::Infinity;
    }
    Rounded::Finite(significand, BigInt::from(quantum))
}

/// The exact decimal `D e Q` of `significand * 2^quantum`, `D` without trailing zeros.
fn exact_decimal(significand: BigUint, quantum: BigInt) -> String {
    let zeros = significand.trailing_zeros().expect("a nonzero significand");
    let odd = significand >> zeros;
    let quantum = quantum + zeros;
    if quantum.is_negative() {
        let power = quantum.magnitude().to_u32().expect("within the bound");
        let digits = odd * BigUint::from(5_u8).pow(power);
        format!("{digits}e{quantum}")
    } else {
        let shift = quantum.to_u64().expect("within the bound");
        let integer = (odd << shift).to_string();
        let trimmed = integer.trim_end_matches('0');
        format!("{trimmed}e{}", integer.len() - trimmed.len())
    }
}

/// `floor(x * log)` for the logarithm bracketed by `(low, high)` over `LOG_SCALE`: a lower bound
/// of `x * log` whatever the sign of `x`.
fn scale_floor(x: &BigInt, (low, high): (u64, u64)) -> BigInt {
    let factor = if x.is_negative() { high } else { low };
    floor_div(&(x * factor), LOG_SCALE)
}

/// `ceil(x * log)`: an upper bound of `x * log` whatever the sign of `x`.
fn scale_ceil(x: &BigInt, (low, high): (u64, u64)) -> BigInt {
    let factor = if x.is_negative() { low } else { high };
    -floor_div(&-(x * factor), LOG_SCALE)
}

fn floor_div(x: &BigInt, divisor: u64) -> BigInt {
    let quotient = x / divisor;
    if x.is_negative() && !(x % divisor).is_zero() {
        quotient - 1
    } else {
        quotient
    }
}

#[cfg(test)]
mod tests;
