//! `rootFloat(x, n)` as IEEE 754 `rootn(x, n)`, rounded to nearest in the format of `x`.
//!
//! IEEE 754 gives `rootn` its special cases (a zero, an infinity, a NaN, `n = 0`, a negative `x`)
//! and asks for the correctly rounded real `x^(1/n)` everywhere else. Degree 1 is `x`, degree -1
//! the IEEE division `1/x`, degree 2 IEEE `squareRoot` (except at -0); no IEEE operation computes
//! any other degree, so the rounding is decided exactly here.
//!
//! For `|n| >= 2` and a finite positive `x` the root `y` lies in the normal range, and it is
//! never a midpoint between two adjacent floats: a midpoint `m` has `p + 1` significant bits, so
//! `m^n` has more than `p` (for `n > 0`), and `m^n` is not a power of two (for `n < 0`, where
//! `x = 1 / m^|n|`), while `x` is a float of `p` significant bits. So `y` rounds to the float
//! whose two neighbouring midpoints enclose it, and `y > m` holds exactly when
//! `log2(x) - n * log2(m)` has the sign of `n`. That sign is computed with logarithms in binary
//! fixed point whose error is bounded, with more bits until the bound separates it from 0; a
//! binary search over the format's positive bit patterns, ordered as the values are, finds the
//! float.

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};

/// The degrees from which every finite positive root rounds to 1. With `|ln x| <= 745` for every
/// finite positive `binary64` (and less for `binary32`), `|ln y| = |ln x| / |n| <= 2^-(p + 2)`
/// once `|n| >= 745 * 2^(p + 2)`, which is below `2^66` for both formats; then `y` lies strictly
/// between the midpoints `1 - 2^-(p + 1)` and `1 + 2^-p` around 1.
const DEGREE_ROUNDING_TO_ONE_BITS: u64 = 66;

/// Guard bits of the fixed-point logarithms: a logarithm computed with `W` fractional bits is
/// within `2W + 25` units of `2^-W` (see [`log2_fixed`]), which is below `2^GUARD_BITS` for
/// every `W` this module uses.
const GUARD_BITS: u64 = 32;

/// An IEEE 754 binary interchange format: its stored fraction bits and its exponent bias.
#[derive(Clone, Copy)]
pub(super) struct Format {
    pub(super) fraction_bits: u32,
    pub(super) bias: i64,
    /// The bit pattern of the largest finite value.
    pub(super) largest_finite: u64,
}

pub(super) const BINARY32: Format = Format {
    fraction_bits: 23,
    bias: 127,
    largest_finite: 0x7f7f_ffff,
};

pub(super) const BINARY64: Format = Format {
    fraction_bits: 52,
    bias: 1023,
    largest_finite: 0x7fef_ffff_ffff_ffff,
};

/// The bit pattern of the correctly rounded `x^(1/n)` for a finite positive `x` (as its bit
/// pattern) and `|n| >= 2`.
pub(super) fn positive_root_bits(format: Format, x: u64, degree: &BigInt) -> u64 {
    debug_assert!(
        degree.magnitude().bits() > 1,
        "degrees 0, 1 and -1 are special cases"
    );
    if degree.magnitude().bits() > DEGREE_ROUNDING_TO_ONE_BITS {
        return one_bits(format);
    }
    let (x_significand, x_exponent) = decode(format, x);
    let mut comparison = Comparison::new(x_significand, x_exponent, degree);
    // Invariant: the root is above the midpoint below `low` and not above the midpoint below
    // `high`; the first holds for the smallest positive float, whose lower midpoint is half of it,
    // far below every root of degree 2 or more, and the second for the pattern after the largest
    // finite value, whose root would exceed every float.
    let (mut low, mut high) = (1, format.largest_finite + 1);
    while high - low > 1 {
        let middle = low + (high - low) / 2;
        let (significand, exponent) = midpoint(format, middle);
        if comparison.root_exceeds(&significand, exponent) {
            low = middle;
        } else {
            high = middle;
        }
    }
    low
}

fn one_bits(format: Format) -> u64 {
    (format.bias as u64) << format.fraction_bits
}

/// The value of a positive finite bit pattern as `significand * 2^exponent`.
fn decode(format: Format, bits: u64) -> (BigUint, i64) {
    let fraction = bits & ((1 << format.fraction_bits) - 1);
    let biased = (bits >> format.fraction_bits) as i64;
    let lowest = 1 - format.bias - i64::from(format.fraction_bits);
    if biased == 0 {
        (BigUint::from(fraction), lowest)
    } else {
        (
            BigUint::from(fraction | (1 << format.fraction_bits)),
            biased - 1 + lowest,
        )
    }
}

/// The midpoint between the floats of bit patterns `bits - 1` and `bits` as
/// `significand * 2^exponent`.
fn midpoint(format: Format, bits: u64) -> (BigUint, i64) {
    let (lower, lower_exponent) = decode(format, bits - 1);
    let (upper, upper_exponent) = decode(format, bits);
    let exponent = lower_exponent.min(upper_exponent);
    let shift = |exponent_of: i64| usize::try_from(exponent_of - exponent).expect("aligned");
    (
        (lower << shift(lower_exponent)) + (upper << shift(upper_exponent)),
        exponent - 1,
    )
}

/// The comparisons of one root `x^(1/n)` with candidate values `m`, each decided by the sign of
/// `log2(x) - n * log2(m)`.
struct Comparison {
    x_significand: BigUint,
    x_exponent: i64,
    degree: BigInt,
    /// The fractional bits of the logarithms, and `log2(ln 2)`'s and `log2(x)`'s values at them.
    precision: u64,
    ln2: BigInt,
    log2_x: BigInt,
}

impl Comparison {
    fn new(x_significand: BigUint, x_exponent: i64, degree: &BigInt) -> Self {
        let precision = 64 + degree.magnitude().bits() + GUARD_BITS;
        let ln2 = ln_ratio(&BigUint::one(), &BigUint::from(3_u8), precision);
        let log2_x = log2_fixed(&x_significand, x_exponent, &ln2, precision);
        Self {
            x_significand,
            x_exponent,
            degree: degree.clone(),
            precision,
            ln2,
            log2_x,
        }
    }

    /// Whether `x^(1/n) > m` for `m = significand * 2^exponent`, which is never equal to the root.
    fn root_exceeds(&mut self, significand: &BigUint, exponent: i64) -> bool {
        // Invariant: `self.ln2` and `self.log2_x` hold `ln 2` and `log2(x)` with
        // `self.precision` fractional bits; each round doubles the precision, and the loop ends
        // once the error bound separates the difference from 0, which it eventually does since
        // the difference is not 0.
        loop {
            let log2_m = log2_fixed(significand, exponent, &self.ln2, self.precision);
            let difference = &self.log2_x - &self.degree * log2_m;
            // Each logarithm is within `2W + 25` units, and the difference combines `log2(x)`
            // with `|n|` copies of `log2(m)`.
            let bound = (BigInt::from(self.degree.magnitude().clone()) + 1u8)
                * BigInt::from(2 * self.precision + 25);
            if difference.abs() > bound {
                return (difference.sign() == Sign::Plus) == (self.degree.sign() == Sign::Plus);
            }
            self.precision *= 2;
            self.ln2 = ln_ratio(&BigUint::one(), &BigUint::from(3_u8), self.precision);
            self.log2_x = log2_fixed(
                &self.x_significand,
                self.x_exponent,
                &self.ln2,
                self.precision,
            );
        }
    }
}

/// `log2(significand * 2^exponent)` with `precision` fractional bits, given `ln 2` at that
/// precision, within `2 * precision + 25` units of the last place.
///
/// With `k + 1` the bit length of the significand, the value is `exponent + k + log2(z)` for
/// `z = significand / 2^k` in `[1, 2)`; the integer part is exact, and `log2(z)` is the quotient
/// `ln(z) / ln 2` of two series ([`ln_ratio`]) each within `2N + 4` units for `N` terms, which
/// the division by about 0.69 turns into at most `6N + 13` units; `N <= precision / 3 + 2`, since
/// each term is at most a ninth of the one before.
fn log2_fixed(significand: &BigUint, exponent: i64, ln2: &BigInt, precision: u64) -> BigInt {
    let k = significand.bits() - 1;
    let power = BigUint::one() << k;
    let ln_z = ln_ratio(&(significand - &power), &(significand + &power), precision);
    let fraction = (ln_z << precision) / ln2;
    ((BigInt::from(exponent) + BigInt::from(k)) << precision) + fraction
}

/// `ln((1 + t) / (1 - t)) = 2 atanh(t)` for `t = numerator / denominator` in `[0, 1/3]`, with
/// `precision` fractional bits: `2 * sum(t^(2j + 1) / (2j + 1))`, every product and quotient
/// rounded down. Each term's rounding error is at most the previous one's (the ratio is below 1)
/// plus one unit, and the omitted tail is below one unit, so the result is within `2N + 4` units
/// for `N` terms.
fn ln_ratio(numerator: &BigUint, denominator: &BigUint, precision: u64) -> BigInt {
    let mut term = (numerator << precision) / denominator;
    let square_numerator = numerator * numerator;
    let square_denominator = denominator * denominator;
    let mut sum = term.clone();
    let mut odd = BigUint::one();
    // Invariant: `term` is `t^(2j + 1)` and `sum` the series up to it, both in fixed point;
    // `term` shrinks by at least a factor 9 per round, so the loop runs at most
    // `precision / 3 + 1` times.
    while !term.is_zero() {
        term = term * &square_numerator / &square_denominator;
        odd += 2_u8;
        sum += &term / &odd;
    }
    BigInt::from(sum << 1)
}

/// The IEEE 754 `rootn` special cases for degree `n` and value `x` (of either format, exactly
/// representable in `f64`): `Some(value)` when `x` is NaN, a zero or an infinity, `n` is 0, or
/// `x` is negative and `n` even; `None` otherwise, where the root has `x`'s sign (an odd root of
/// a negative value is the negation of the root of its magnitude).
pub(super) fn special_root(x: f64, degree: &BigInt) -> Option<f64> {
    let odd = degree.magnitude().bit(0);
    if x.is_nan() || degree.is_zero() || (x < 0.0 && !odd) {
        return Some(f64::NAN);
    }
    let positive_degree = degree.is_positive();
    if x == 0.0 {
        let sign = if odd { x.signum() } else { 1.0 };
        return Some(if positive_degree {
            0.0 * sign
        } else {
            f64::INFINITY * sign
        });
    }
    if x.is_infinite() {
        let sign = x.signum();
        return Some(if positive_degree {
            f64::INFINITY * sign
        } else {
            0.0 * sign
        });
    }
    None
}

/// Whether `degree` is 1, -1 or 2, the degrees IEEE operations compute.
pub(super) fn native_degree(degree: &BigInt) -> Option<i8> {
    degree.to_i8().filter(|degree| matches!(degree, -1 | 1 | 2))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn root64(x: f64, degree: i64) -> f64 {
        f64::from_bits(positive_root_bits(
            BINARY64,
            x.to_bits(),
            &BigInt::from(degree),
        ))
    }

    fn root32(x: f32, degree: i64) -> f32 {
        f32::from_bits(
            u32::try_from(positive_root_bits(
                BINARY32,
                u64::from(x.to_bits()),
                &BigInt::from(degree),
            ))
            .unwrap(),
        )
    }

    /// Exact roots are found exactly, and degree 2 agrees with IEEE `squareRoot`, which is
    /// correctly rounded, on values whose root is not exact.
    #[test]
    fn roots_are_exact_where_exact_and_agree_with_the_ieee_square_root() {
        assert_eq!(root64(27.0, 3), 3.0);
        assert_eq!(root64(1024.0, 10), 2.0);
        assert_eq!(root64(16.0, -4), 0.5);
        assert_eq!(root64(0.125, -3), 2.0);
        assert_eq!(root64(3f64.powi(33), 33), 3.0);
        assert_eq!(root32(27.0, 3), 3.0);
        assert_eq!(root32(0.0625, -4), 2.0);
        for x in [2.0, 3.0, 1e-300, 1e300, 5e-324, f64::MAX, 0.1, 7.0] {
            assert_eq!(root64(x, 2), x.sqrt(), "sqrt({x:e})");
        }
        for x in [2.0f32, 3.0, 1e-40, 1e38, f32::MAX, 0.1] {
            assert_eq!(root32(x, 2), x.sqrt(), "sqrt({x:e})");
        }
    }

    /// `a * 2^e` as a numerator and denominator.
    fn ratio(significand: BigUint, exponent: i64) -> (BigUint, BigUint) {
        let shift = usize::try_from(exponent.unsigned_abs()).unwrap();
        if exponent >= 0 {
            (significand << shift, BigUint::one())
        } else {
            (significand, BigUint::one() << shift)
        }
    }

    /// Whether `x^(1/n) > m` by exact integer arithmetic: `x > m^n` for `n > 0`, `x * m^|n| < 1`
    /// for `n < 0`.
    fn exceeds_exactly(x: f64, degree: i64, m: (BigUint, i64)) -> bool {
        let (x_numerator, x_denominator) = ratio(
            decode(BINARY64, x.to_bits()).0,
            decode(BINARY64, x.to_bits()).1,
        );
        let (m_numerator, m_denominator) = ratio(m.0, m.1);
        let power = u32::try_from(degree.unsigned_abs()).unwrap();
        let (m_numerator, m_denominator) = (m_numerator.pow(power), m_denominator.pow(power));
        if degree > 0 {
            x_numerator * m_denominator > m_numerator * x_denominator
        } else {
            x_numerator * m_numerator < x_denominator * m_denominator
        }
    }

    /// For small degrees the result is checked with exact integer arithmetic: the root lies
    /// strictly between the midpoints below and above the returned float.
    #[test]
    fn the_root_lies_between_the_midpoints_around_the_result() {
        let values = [
            2.0,
            3.0,
            10.0,
            0.1,
            123.456,
            1e-300,
            1e300,
            5e-324,
            2.2250738585072014e-308,
            f64::MAX,
            1.0 + f64::EPSILON,
            1.0 - f64::EPSILON / 2.0,
        ];
        for x in values {
            for degree in (-7..=-2).chain(2..=7) {
                let bits = positive_root_bits(BINARY64, x.to_bits(), &BigInt::from(degree));
                let below = midpoint(BINARY64, bits);
                let above = midpoint(BINARY64, bits + 1);
                assert!(
                    exceeds_exactly(x, degree, below) && !exceeds_exactly(x, degree, above),
                    "rootn({x:e}, {degree}) = {:e}",
                    f64::from_bits(bits)
                );
            }
        }
    }

    #[test]
    fn large_degrees_are_rounded() {
        // A degree beyond 2^66 rounds every finite positive value to 1.
        assert_eq!(
            f64::from_bits(positive_root_bits(
                BINARY64,
                f64::MAX.to_bits(),
                &(BigInt::from(1) << 70)
            )),
            1.0
        );
    }
}
