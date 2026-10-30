//! The binary32 destination of a Float operation over a binary32 and a binary64 operand, the
//! value another model of the definition gives where k-rust's reading takes binary64
//! (`super::MixedPair`), for the test-only chooser (`crate::choice_sampling`).
//!
//! IEEE 754 defines an operation as its exact result rounded once to the destination format. The
//! exact result is first rounded to binary64 (`p`, the native operation on the widened operands)
//! and then to odd: `p` when `p` is the exact result or `p`'s last significand bit is odd, else
//! the binary64 neighbour of `p` on the exact result's side. The exact result lies strictly
//! between `p` and that neighbour when it is not `p`, because `p` is one of the two binary64
//! values around it, and of two adjacent binary64 values exactly one has an odd last bit. A value
//! rounded to odd at precision 53 and then to nearest at precision 24 or less (binary32, its
//! subnormals included, whose spacing is at least 2^29 times binary64's there) is the exact value
//! rounded to nearest: rounding to odd keeps it strictly on the same side of every binary32
//! midpoint, and a midpoint itself is kept, since it is a binary64 value. Binary32's overflow is
//! decided on that rounded value, as the conversion `as f32` decides it.
//!
//! Only the side of the exact result relative to `p` is needed, and it is computed exactly over
//! the integers (every finite binary64 value is an integer times a power of two). When an operand
//! is infinite or NaN, the IEEE result is exact (an infinity, a NaN or a signed zero), and when
//! `p` overflows, the exact result exceeds binary32's range as well; in both cases `p as f32` is
//! the binary32 result.

use std::cmp::Ordering;

use num_bigint::{BigInt, Sign};

use super::BinaryOperation;

/// `operation` applied to the binary64 values `left` and `right` (one of them a widened binary32
/// value), its exact result rounded once to nearest, ties to even, in binary32.
pub(super) fn binary32_destination(operation: BinaryOperation, left: f64, right: f64) -> f32 {
    let rounded = operation.binary64(left, right);
    let side = if left.is_finite() && right.is_finite() && rounded.is_finite() {
        exact_side(operation, left, right, rounded)
    } else {
        Ordering::Equal
    };
    round_to_odd(rounded, side) as f32
}

/// Where the exact result of `operation` on the finite `left` and `right` lies relative to
/// `rounded`, its finite binary64 rounding: `Greater` above it, `Less` below, `Equal` at it.
fn exact_side(operation: BinaryOperation, left: f64, right: f64, rounded: f64) -> Ordering {
    let (left, right, rounded) = (dyadic(left), dyadic(right), dyadic(rounded));
    match operation {
        BinaryOperation::Add => sign_of_sum(&[left, right, negated(rounded)]),
        BinaryOperation::Sub => sign_of_sum(&[left, negated(right), negated(rounded)]),
        BinaryOperation::Mul => sign_of_sum(&[product(&left, &right), negated(rounded)]),
        // `left / right - rounded` has the sign of `left - right * rounded` times `right`'s; a
        // finite quotient of finite operands has a nonzero divisor.
        BinaryOperation::Div => {
            let remainder = sign_of_sum(&[left, negated(product(&right, &rounded))]);
            if right.0.sign() == Sign::Minus {
                remainder.reverse()
            } else {
                remainder
            }
        }
        // `fp.min` and `fp.max` give an operand, which binary64 holds exactly.
        BinaryOperation::Min | BinaryOperation::Max => Ordering::Equal,
    }
}

/// `rounded` rounded to odd toward an exact value on `side` of it (see the module documentation):
/// `rounded` when `side` is `Equal` or its last significand bit is odd, else its binary64
/// neighbour on `side`. A zero's neighbour on either side is the least subnormal of that sign.
/// `rounded` is finite when `side` is not `Equal`.
pub(super) fn round_to_odd(rounded: f64, side: Ordering) -> f64 {
    let bits = rounded.to_bits();
    if side == Ordering::Equal || bits & 1 == 1 {
        return rounded;
    }
    if rounded == 0.0 {
        let least = f64::from_bits(1);
        return if side == Ordering::Greater {
            least
        } else {
            -least
        };
    }
    // Away from zero is the next bit pattern, toward zero the previous one, on either sign; an
    // even pattern below the largest finite one (odd) never steps to an infinity, and a nonzero
    // one never steps across zero.
    let away = (side == Ordering::Greater) == (rounded > 0.0);
    f64::from_bits(if away { bits + 1 } else { bits - 1 })
}

/// A finite binary64 value as an integer and a power of two: `value = integer * 2^exponent`.
fn dyadic(value: f64) -> (BigInt, i32) {
    debug_assert!(value.is_finite());
    let bits = value.to_bits();
    let biased = ((bits >> 52) & 0x7ff) as i32;
    let fraction = bits & ((1 << 52) - 1);
    let (significand, exponent) = if biased == 0 {
        (fraction, -1074)
    } else {
        (fraction | (1 << 52), biased - 1075)
    };
    let significand = BigInt::from(significand);
    (
        if value.is_sign_negative() {
            -significand
        } else {
            significand
        },
        exponent,
    )
}

fn negated((integer, exponent): (BigInt, i32)) -> (BigInt, i32) {
    (-integer, exponent)
}

fn product(left: &(BigInt, i32), right: &(BigInt, i32)) -> (BigInt, i32) {
    (&left.0 * &right.0, left.1 + right.1)
}

/// The sign of the exact sum of `terms`, each brought to the least exponent among them.
fn sign_of_sum(terms: &[(BigInt, i32)]) -> Ordering {
    let least = terms
        .iter()
        .map(|(_, exponent)| *exponent)
        .min()
        .expect("a sum of at least one term");
    let sum: BigInt = terms
        .iter()
        .map(|(integer, exponent)| integer << (exponent - least) as usize)
        .sum();
    match sum.sign() {
        Sign::Minus => Ordering::Less,
        Sign::NoSign => Ordering::Equal,
        Sign::Plus => Ordering::Greater,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Signed, Zero};

    /// The exact result of `operation` on two finite binary64 values (Min and Max excluded), as
    /// a fraction with a positive denominator.
    fn exact(operation: BinaryOperation, left: f64, right: f64) -> (BigInt, BigInt) {
        let fraction = |(integer, exponent): (BigInt, i32)| {
            if exponent >= 0 {
                (integer << exponent as usize, BigInt::one())
            } else {
                (integer, BigInt::one() << (-exponent) as usize)
            }
        };
        let (left, right) = (fraction(dyadic(left)), fraction(dyadic(right)));
        let (numerator, denominator) = match operation {
            BinaryOperation::Add => (&left.0 * &right.1 + &right.0 * &left.1, &left.1 * &right.1),
            BinaryOperation::Sub => (&left.0 * &right.1 - &right.0 * &left.1, &left.1 * &right.1),
            BinaryOperation::Mul => (&left.0 * &right.0, &left.1 * &right.1),
            BinaryOperation::Div => (&left.0 * &right.1, &left.1 * &right.0),
            BinaryOperation::Min | BinaryOperation::Max => unreachable!("not compared"),
        };
        if denominator.is_negative() {
            (-numerator, -denominator)
        } else {
            (numerator, denominator)
        }
    }

    /// The fraction `numerator / denominator` (`denominator > 0`) rounded to nearest, ties to
    /// even, in binary32, by integer division alone: the magnitude is scaled by `2^-k` into
    /// `[2^23, 2^24)` (with `k >= -149`, the subnormal spacing), truncated, and rounded by the
    /// remainder; a magnitude of `2^128` or more after rounding is an infinity. The sign of a zero
    /// result is the fraction's (a zero fraction is +0: the callers' zero results are checked
    /// apart).
    fn binary32_of_fraction(numerator: &BigInt, denominator: &BigInt) -> f32 {
        let negative = numerator.is_negative();
        let magnitude = numerator.abs();
        if magnitude.is_zero() {
            return 0.0;
        }
        // The least k with magnitude / denominator < 2^(k + 24), then at least -149.
        let mut k = magnitude.bits() as i64 - denominator.bits() as i64 - 24;
        let below = |k: i64| {
            if k + 24 >= 0 {
                magnitude < (denominator << ((k + 24) as usize))
            } else {
                (magnitude.clone() << ((-(k + 24)) as usize)) < *denominator
            }
        };
        while !below(k) {
            k += 1;
        }
        while below(k - 1) {
            k -= 1;
        }
        let k = k.max(-149);
        let (scaled_numerator, scaled_denominator) = if k >= 0 {
            (magnitude.clone(), denominator << k as usize)
        } else {
            (magnitude.clone() << (-k) as usize, denominator.clone())
        };
        let quotient = &scaled_numerator / &scaled_denominator;
        let twice_remainder: BigInt =
            (&scaled_numerator - &quotient * &scaled_denominator) << 1usize;
        let mut significand: u64 = quotient.try_into().expect("below 2^24");
        match twice_remainder.cmp(&scaled_denominator) {
            Ordering::Greater => significand += 1,
            Ordering::Equal if significand & 1 == 1 => significand += 1,
            _ => {}
        }
        let value = if k + i64::from(64 - significand.leading_zeros() as i32) > 128 {
            f32::INFINITY
        } else {
            // Exact: at most 25 significant bits at an exponent binary64 holds, and then a value
            // binary32 holds.
            ((significand as f64) * 2f64.powi(k as i32)) as f32
        };
        if negative { -value } else { value }
    }

    fn checked(operation: BinaryOperation, left: f64, right: f64) -> f32 {
        let (numerator, denominator) = exact(operation, left, right);
        let expected = binary32_of_fraction(&numerator, &denominator);
        let found = binary32_destination(operation, left, right);
        if expected == 0.0 {
            assert_eq!(found, 0.0, "{left:e} {right:e}");
        } else {
            assert_eq!(
                found.to_bits(),
                expected.to_bits(),
                "{left:e}, {right:e}: {found:e} for {expected:e}"
            );
        }
        found
    }

    const OPERATIONS: [BinaryOperation; 4] = [
        BinaryOperation::Add,
        BinaryOperation::Sub,
        BinaryOperation::Mul,
        BinaryOperation::Div,
    ];

    fn widened(value: f32) -> f64 {
        f64::from(value)
    }

    fn next_up(value: f64) -> f64 {
        f64::from_bits(value.to_bits() + 1)
    }

    #[test]
    fn round_to_odd_keeps_an_exact_or_odd_value_and_steps_an_even_one_toward_the_exact_side() {
        let even = 1.0;
        let odd = next_up(1.0);
        assert_eq!(round_to_odd(even, Ordering::Equal), even);
        assert_eq!(round_to_odd(odd, Ordering::Greater), odd);
        assert_eq!(round_to_odd(odd, Ordering::Less), odd);
        assert_eq!(round_to_odd(even, Ordering::Greater), odd);
        // Below a power of two the spacing halves: the neighbour is the largest value below.
        assert_eq!(
            round_to_odd(even, Ordering::Less),
            f64::from_bits(even.to_bits() - 1)
        );
        assert_eq!(round_to_odd(-even, Ordering::Less), -odd);
        assert_eq!(
            round_to_odd(-even, Ordering::Greater),
            -f64::from_bits(even.to_bits() - 1)
        );
        assert_eq!(round_to_odd(0.0, Ordering::Greater), f64::from_bits(1));
        assert_eq!(round_to_odd(-0.0, Ordering::Less), -f64::from_bits(1));
        assert_eq!(round_to_odd(f64::MAX, Ordering::Greater), f64::MAX);
        let subnormal = f64::from_bits(2);
        assert_eq!(round_to_odd(subnormal, Ordering::Less), f64::from_bits(1));
    }

    #[test]
    fn exact_results_are_kept() {
        assert_eq!(checked(BinaryOperation::Add, widened(0.5), 2.0), 2.5);
        assert_eq!(checked(BinaryOperation::Mul, widened(0.75), 4.0), 3.0);
        assert_eq!(checked(BinaryOperation::Div, widened(3.0), 0.5), 6.0);
        assert_eq!(
            binary32_destination(BinaryOperation::Min, widened(0.1), 0.1),
            0.1f64 as f32
        );
        assert_eq!(
            binary32_destination(BinaryOperation::Max, widened(0.1), 0.1),
            0.1f32
        );
        let sum = binary32_destination(BinaryOperation::Add, widened(-0.0), -0.0);
        assert!(sum == 0.0 && sum.is_sign_negative());
        let sum = binary32_destination(BinaryOperation::Add, widened(-0.0), 0.0);
        assert!(sum == 0.0 && sum.is_sign_positive());
    }

    /// The exact result just off a binary32 midpoint, which its binary64 rounding hits: rounding
    /// twice to nearest would take the midpoint's even neighbour, on the wrong side.
    #[test]
    fn a_result_near_a_binary32_midpoint_rounds_to_its_own_side() {
        let half = 2f64.powi(-24);
        let off = 2f64.powi(-70);
        let above_one = 1.0 + 2f64.powi(-23);
        // 1 + 2^-24 + 2^-70 is above the midpoint of 1 and 1 + 2^-23, its binary64 rounding is
        // the midpoint, and 1, the even neighbour, is below.
        assert_eq!((1.0 + (half + off)) as f32, 1.0, "double rounding errs");
        assert_eq!(
            checked(BinaryOperation::Add, 1.0, half + off),
            above_one as f32
        );
        // 1 + 2^-23 + 2^-24 - 2^-70 is below the midpoint of 1 + 2^-23 (odd) and 1 + 2^-22.
        assert_eq!(
            (above_one + (half - off)) as f32,
            (1.0 + 2f64.powi(-22)) as f32,
            "double rounding errs"
        );
        assert_eq!(
            checked(BinaryOperation::Add, above_one, half - off),
            above_one as f32
        );
        assert_eq!(
            checked(BinaryOperation::Sub, above_one, off - half),
            above_one as f32
        );
        // Exactly at a midpoint: ties to even.
        assert_eq!(checked(BinaryOperation::Add, 1.0, half), 1.0);
        assert_eq!(
            checked(BinaryOperation::Add, above_one, half),
            (1.0 + 2f64.powi(-22)) as f32
        );
        // A product and a quotient just off the midpoint 1 + 2^-24.
        assert_eq!(
            checked(BinaryOperation::Mul, widened(1.0), next_up(1.0 + half)),
            above_one as f32
        );
        checked(
            BinaryOperation::Div,
            widened(2.0),
            2.0 / next_up(1.0 + half),
        );
        checked(
            BinaryOperation::Div,
            widened(3.0),
            3.0 / next_up(1.0 + half),
        );
    }

    #[test]
    fn subnormal_results_round_on_binary32_spacing() {
        let least = f32::from_bits(1);
        // 2^-150, the midpoint of 0 and the least subnormal: ties to even, +0.
        assert_eq!(checked(BinaryOperation::Mul, widened(least), 0.5), 0.0);
        // Just above it: the least subnormal.
        assert_eq!(
            checked(BinaryOperation::Mul, widened(least), 0.5 + 2f64.powi(-50)),
            least
        );
        // 1.5 * least - 2^-203, a quarter of binary64's spacing below the midpoint of least and
        // 2 * least, which binary64 rounds to: the even 2 * least would be on the wrong side.
        let below_midpoint = 2f64.powi(-150) - 2f64.powi(-203);
        assert_eq!(
            (widened(least) + below_midpoint) as f32,
            f32::from_bits(2),
            "double rounding errs"
        );
        assert_eq!(
            checked(BinaryOperation::Add, widened(least), below_midpoint),
            least
        );
        assert_eq!(
            checked(BinaryOperation::Div, widened(least), 2.0 - 2f64.powi(-51)),
            least
        );
        // Three halves of the least subnormal: a tie, to the even 2 * least.
        assert_eq!(
            checked(BinaryOperation::Mul, widened(least), 1.5),
            f32::from_bits(2)
        );
        // Far below every binary32 value: a zero of the exact result's sign, also where binary64
        // rounds the exact result to zero.
        let tiny = binary32_destination(BinaryOperation::Mul, widened(-least), 1e-300);
        assert!(tiny == 0.0 && tiny.is_sign_negative());
        let tiny = binary32_destination(BinaryOperation::Div, widened(least), -1e300);
        assert!(tiny == 0.0 && tiny.is_sign_negative());
        // The largest subnormal and the least normal value.
        let largest_subnormal = f32::from_bits(0x007f_ffff);
        assert_eq!(
            checked(
                BinaryOperation::Add,
                widened(largest_subnormal),
                2f64.powi(-150) + 2f64.powi(-200)
            ),
            f32::MIN_POSITIVE
        );
    }

    #[test]
    fn a_result_past_binary32_range_is_an_infinity() {
        let max = widened(f32::MAX);
        let half_spacing = 2f64.powi(103);
        // The midpoint of the largest binary32 value (odd) and 2^128 rounds to 2^128: infinity.
        assert_eq!(
            checked(BinaryOperation::Add, max, half_spacing),
            f32::INFINITY
        );
        // Just below it binary64 rounds to the midpoint, and the result is the largest value.
        assert_eq!(
            (max + (half_spacing - 2f64.powi(50))) as f32,
            f32::INFINITY,
            "double rounding errs"
        );
        assert_eq!(
            checked(BinaryOperation::Add, max, half_spacing - 2f64.powi(50)),
            f32::MAX
        );
        assert_eq!(
            checked(BinaryOperation::Sub, -max, half_spacing + 2f64.powi(50)),
            f32::NEG_INFINITY
        );
        assert_eq!(
            checked(BinaryOperation::Mul, widened(2f32.powi(127)), 4.0),
            f32::INFINITY
        );
        // Binary64 overflow, and the infinities and NaN of the operands.
        assert_eq!(
            binary32_destination(BinaryOperation::Mul, widened(f32::MAX), f64::MAX),
            f32::INFINITY
        );
        assert_eq!(
            binary32_destination(BinaryOperation::Add, f64::MAX, widened(f32::MAX)),
            f32::INFINITY
        );
        assert_eq!(
            binary32_destination(BinaryOperation::Sub, widened(1.0), f64::INFINITY),
            f32::NEG_INFINITY
        );
        assert!(binary32_destination(BinaryOperation::Div, widened(0.0), 0.0).is_nan());
        let quotient = binary32_destination(BinaryOperation::Div, widened(-1.0), f64::INFINITY);
        assert!(quotient == 0.0 && quotient.is_sign_negative());
    }

    /// Exact results near every binary32 midpoint of a spread of binary32 values, normal and
    /// subnormal, by each operation, against the exact fraction rounded by integer division; and
    /// rounding twice to nearest errs on some of them, so they test the rounding to odd.
    #[test]
    fn results_near_midpoints_and_random_pairs_round_as_their_exact_values() {
        let mut state = 0x2545_f491_4f6c_dd1d_u64;
        let mut random = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut double_rounding_errs = 0;
        for _ in 0..4000 {
            let single = f32::from_bits((random() as u32) % 0x7f80_0000);
            let single = if random() & 1 == 1 { -single } else { single };
            let value = widened(single);
            let spacing = widened(f32::from_bits(single.to_bits() + 1)) - value;
            if !spacing.is_finite() {
                continue;
            }
            for nudge in [-1.0, 0.0, 1.0] {
                let offset = spacing / 2.0 + nudge * spacing * 2f64.powi(-31);
                let naive = (value + offset) as f32;
                let found = checked(BinaryOperation::Add, value, offset);
                double_rounding_errs += usize::from(naive != found);
                checked(BinaryOperation::Sub, value, -offset);
                let factor = 1.0 + offset / value;
                if value != 0.0 && factor.is_finite() {
                    checked(BinaryOperation::Mul, value, factor);
                    checked(BinaryOperation::Div, value, 1.0 / factor);
                }
            }
            let double = f64::from_bits(random() % 0x7ff0_0000_0000_0000);
            let double = if random() & 1 == 1 { -double } else { double };
            // A binary64 operand near the binary32 one's magnitude, and one of any magnitude.
            let near = value * (1.0 + (random() >> 12) as f64 * 2f64.powi(-52));
            for other in [double, near] {
                for operation in OPERATIONS {
                    for (left, right) in [(value, other), (other, value)] {
                        if operation.binary64(left, right).is_finite() {
                            checked(operation, left, right);
                        }
                    }
                }
            }
        }
        assert!(
            double_rounding_errs > 0,
            "the midpoints test the rounding to odd"
        );
    }
}
