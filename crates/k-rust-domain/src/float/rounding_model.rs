//! The exact rounding of a positive rational to an IEEE-like format, in rational arithmetic on
//! big integers: the model the canonical Float text (`canonical_float_text`) and the backend's
//! Float hooks are checked against. Built for this crate's tests and with the test feature
//! `rounding-model`, which the backend's tests enable; no normal build has it.

use num_bigint::BigUint;
use num_traits::Zero;

/// The positive `num/den` rounded to nearest, ties to even, with `precision` significant bits
/// (the implicit bit included) and the normal exponents `emin..=emax`, subnormals included:
/// `Some((mantissa, quantum))` for the value `mantissa·2^quantum` (a zero mantissa when it rounds
/// to zero), and `None` when it overflows to infinity. The arithmetic of the backend's Float
/// hook models' rounding for any IEEE-like format, which the canonical text of Float literals is
/// also checked against.
pub fn round_exact(
    precision: i64,
    emin: i64,
    emax: i64,
    num: &BigUint,
    den: &BigUint,
) -> Option<(BigUint, i64)> {
    let mut exponent = num.bits() as i64 - den.bits() as i64;
    if !at_least_power(num, den, exponent) {
        exponent -= 1;
    }
    let mut quantum = exponent.max(emin) - (precision - 1);
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
    if !mantissa.is_zero() && quantum + mantissa.bits() as i64 - 1 > emax {
        return None;
    }
    Some((mantissa, quantum))
}

/// `num/den ≥ 2^power`.
fn at_least_power(num: &BigUint, den: &BigUint, power: i64) -> bool {
    if power >= 0 {
        *num >= den << power
    } else {
        num << -power >= *den
    }
}
