//! Which Float literals name an element the literal rule leaves open.
//!
//! `domains.md` gives a literal's value by its mantissa and exponent, "rounded to the nearest
//! possible value" in the format its suffix names (its "Floating-point numbers" section). That
//! fixes the element where one value of the format is nearest; it leaves the element open
//!
//! - at a tie, a rational exactly between two adjacent values of the format: "nearest" names two;
//! - at or beyond the overflow threshold, half an ulp past the largest finite value: "nearest"
//!   gives the largest finite value, and k-rust, rounding like an IEEE 754 format, infinity;
//! - for a nonzero rational that rounds to a zero, below or at half the least subnormal: both
//!   zeros are equally near, and no text says which one a nonzero value becomes;
//! - for an `Infinity` lexeme, which no value rule names.
//!
//! A zero literal names the zero of its written sign, and a `NaN` literal the one NaN of its
//! format (`docs/compatibility.md`, "Backend scope"): neither is open. The decision is exact: the
//! rational is compared with the format's values and midpoints in integer arithmetic, so a tie
//! and the overflow threshold are decided on the literal's own digits, never on a rounded double.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive};

use super::{Literal, Magnitude, Other, Outcome, Rounded, round_classified, scale_ceil};

/// `log10(2)` and `log10(5)` bracketed by rationals over `10^9`.
const LOG10_2: (u64, u64) = (301_029_995, 301_029_996);
const LOG10_5: (u64, u64) = (698_970_004, 698_970_005);

/// Whether the Float literal `token` names an element the literal rule leaves open: a tie, a
/// magnitude at or beyond half an ulp past the largest finite value, a nonzero value that rounds
/// to a zero, or an `Infinity` lexeme, in the format its suffix names, every spelling of the
/// mantissa and exponent alike. `false` for every other literal, and for a text the load refuses
/// (outside FLOAT-SYNTAX, a format field of 0 or 1, beyond the bound of the canonical text),
/// which names no element k-rust builds.
pub fn literal_open(token: &str) -> bool {
    let Ok(literal) = Literal::parse(token) else {
        return false;
    };
    match literal {
        Literal::Binary32(body) => open(binary(body, 24, 8)),
        Literal::Binary64(body) => open(binary(body, 53, 11)),
        Literal::Other(other) => open(other),
    }
}

/// The literal body `body` in the IEEE-like format of `precision` and `exponent_bits`.
fn binary(body: &str, precision: u8, exponent_bits: u8) -> Other<'_> {
    let (negative, magnitude) = Magnitude::parse(body);
    Other {
        negative,
        magnitude,
        precision: BigUint::from(precision),
        exponent_bits: BigUint::from(exponent_bits),
        _body: body,
    }
}

fn open(mut other: Other<'_>) -> bool {
    let truncation = match &other.magnitude {
        Magnitude::NaN | Magnitude::Zero => return false,
        Magnitude::Infinity => return true,
        Magnitude::Remote { .. } => None,
        Magnitude::Finite { digits, exponent } => {
            critical_digits(&other.precision, &other.exponent_bits)
                .and_then(|keep| truncated(digits, exponent, &keep))
        }
    };
    // A literal longer than every critical point is read through its first digits: it lies
    // strictly between them and the next number of their length, a gap that holds no value of
    // the format and no midpoint, so it rounds as a value just above them does, and is no tie.
    let sticky = truncation.is_some();
    if let Some((digits, exponent)) = truncation {
        other.magnitude = Magnitude::Finite { digits, exponent };
    }
    let Ok(plan) = other.plan() else {
        return false;
    };
    match plan.outcome {
        // A finite nonzero magnitude that the exponent bounds alone decide: beyond the overflow
        // threshold or below half the least subnormal.
        Outcome::Text(_) => true,
        Outcome::Exact => false,
        Outcome::Round {
            significand,
            exponent,
            precision,
            range,
        } => {
            let (rounded, tie) =
                round_classified(significand, &exponent, precision, &range, sticky);
            tie || matches!(rounded, Rounded::Zero | Rounded::Infinity)
        }
    }
}

/// A bound on the significant decimal digits of every critical point of the format: its values,
/// the midpoints of two adjacent values, and the overflow threshold. Each is `m * 2^s` with
/// `m < 2^(N+1)`, `s >= emin - N` and at most `2^(emax+1)`, so it is an integer of at most
/// `(emax+1) log10 2 + 1` digits, or `m * 5^-s / 10^-s` with at most
/// `(N+1) log10 2 + (N - emin) log10 5 + 1`. `None` for an exponent field beyond 64 bits, whose
/// range the plan reads as unbounded and whose literals the canonical text's bound covers.
fn critical_digits(precision: &BigUint, exponent_bits: &BigUint) -> Option<BigInt> {
    let exponent_bits = exponent_bits.to_u64().filter(|bits| *bits <= 64)?;
    let emax: BigInt = (BigInt::one() << (exponent_bits - 1)) - 1;
    let emin: BigInt = 1 - &emax;
    let precision = BigInt::from(precision.clone());
    let integer: BigInt = scale_ceil(&(&emax + 1), LOG10_2) + 1;
    let fraction: BigInt =
        scale_ceil(&(&precision + 1), LOG10_2) + scale_ceil(&(&precision - &emin), LOG10_5) + 1;
    Some(integer.max(fraction) + 2)
}

/// `digits * 10^exponent` cut to its first `keep` digits, without their trailing zeros, when it
/// has more. Every critical point within the literal's decade has at most `keep - 2` significant
/// digits ([`critical_digits`]), so it is a multiple of the last kept digit's place, and the
/// literal, whose dropped digits end in a nonzero one, lies strictly inside a gap between two
/// such multiples.
fn truncated(digits: &str, exponent: &BigInt, keep: &BigInt) -> Option<(String, BigInt)> {
    let keep = keep.to_usize()?;
    if digits.len() <= keep {
        return None;
    }
    let head = digits[..keep].trim_end_matches('0');
    Some((head.to_owned(), exponent + (digits.len() - head.len())))
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use super::literal_open;

    /// The overflow threshold of binary64, `2^1024 - 2^970`, as an integer literal.
    fn binary64_threshold() -> String {
        ((BigUint::from(1_u8) << 1024_u32) - (BigUint::from(1_u8) << 970_u32)).to_string()
    }

    #[test]
    fn a_tie_of_nearest_is_open_in_every_spelling() {
        for token in [
            "9007199254740993",
            "9007199254740993.0",
            "0009007199254740993.000e0",
            "9.007199254740993E15",
            "90071992547409930e-1",
            "+9007199254740993",
            "-9007199254740993d",
            "9007199254740995D",
            "9007199254740993p53x11",
            "9007199254740993p053x0011",
            "16777217f",
            "16777217.0F",
            "-1.6777217e7f",
            "2049p11x5",
        ] {
            assert!(literal_open(token), "{token}");
        }
        for token in [
            "9007199254740992",
            "9007199254740994",
            "9007199254740993.0000000000000000001",
            "9007199254740992.9999999999999999999",
            "16777216f",
            "16777218f",
            "2050p11x5",
            "1.0001p11x5",
        ] {
            assert!(!literal_open(token), "{token}");
        }
    }

    #[test]
    fn the_overflow_threshold_is_decided_on_the_rational() {
        let threshold = binary64_threshold();
        let below = (threshold.parse::<BigUint>().unwrap() - 1_u8).to_string();
        assert!(literal_open(&threshold), "the threshold is a tie");
        assert!(literal_open(&format!("{threshold}.0000001")));
        assert!(!literal_open(&below));
        assert!(!literal_open(&format!("{below}.9999999")));
        assert!(
            !literal_open("1.7976931348623157e308"),
            "the largest finite value"
        );
        assert!(
            !literal_open("1.7976931348623158e308"),
            "below the threshold"
        );
        assert!(literal_open("1.7976931348623159e308"));
        assert!(literal_open("1.0e400"));
        assert!(literal_open("-1.0e400"));
        assert!(literal_open("1e100000000000000000000000"));
        // binary32: `2^128 - 2^103` is 340282356779733661637539395458142568448.
        assert!(literal_open("340282356779733661637539395458142568448f"));
        assert!(!literal_open("340282356779733661637539395458142568447f"));
        assert!(!literal_open("3.4028235e38f"));
        assert!(literal_open("3.4028236e38f"));
        // p11x5: the largest finite value 65504, the threshold 65520.
        assert!(literal_open("65520p11x5"));
        assert!(!literal_open("65519p11x5"));
        assert!(!literal_open("65504p11x5"));
    }

    #[test]
    fn a_nonzero_value_rounding_to_a_zero_is_open() {
        // Half the least binary64 subnormal is `2^-1075`, `5^1075 * 10^-1075`.
        let half = format!("{}e-1075", BigUint::from(5_u8).pow(1075));
        assert!(literal_open(&half), "half the least subnormal is a tie");
        assert!(literal_open(&format!("-{half}")));
        assert!(literal_open("2.4703282292062327e-324"));
        assert!(!literal_open("2.4703282292062328e-324"));
        assert!(
            !literal_open("4.9406564584124654e-324"),
            "the least subnormal"
        );
        assert!(literal_open("1.0e-400"));
        assert!(literal_open("-1.0e-400"));
        assert!(literal_open("1e-100000000000000000000000"));
        assert!(literal_open("1e-46f"));
        assert!(!literal_open("1e-45f"));
    }

    #[test]
    fn zeros_nans_and_unique_nearest_values_are_determined_and_infinities_open() {
        for token in [
            "0.0",
            "-0.0",
            "0e5",
            "-0.000e-99",
            "0.0f",
            "-0p11x5",
            "+0.0d",
            "NaN",
            "NaNf",
            "NaNp11x5",
            "0.1",
            "0.1f",
            "1.0",
            "2.5e-3",
            "1.0p11x5",
        ] {
            assert!(!literal_open(token), "{token}");
        }
        for token in [
            "Infinity",
            "-Infinity",
            "+Infinity",
            "Infinityf",
            "-InfinityD",
            "Infinityp11x5",
        ] {
            assert!(literal_open(token), "{token}");
        }
        for token in ["abc", "1.0p0x11", "1.0p1x11", ""] {
            assert!(
                !literal_open(token),
                "{token} names no element k-rust builds"
            );
        }
    }

    /// A literal longer than every critical point is decided on its first digits and the
    /// knowledge that its dropped digits are not all zero.
    #[test]
    fn a_long_literal_is_decided_as_exactly_as_a_short_one() {
        let zeros = "0".repeat(5000);
        assert!(literal_open(&format!("9007199254740993.{zeros}")));
        assert!(!literal_open(&format!("9007199254740993.{zeros}1")));
        assert!(!literal_open(&format!("9007199254740992.{zeros}1")));
        assert!(!literal_open(&format!("0.1{zeros}1")));
        let threshold = binary64_threshold();
        assert!(literal_open(&format!("{threshold}.{zeros}1")));
        let below = (threshold.parse::<BigUint>().unwrap() - 1_u8).to_string();
        assert!(!literal_open(&format!("{below}.{}", "9".repeat(5000))));
        let fives = BigUint::from(5_u8).pow(1075);
        assert!(literal_open(&format!("{fives}.{zeros}e-1075")));
        assert!(!literal_open(&format!("{fives}.{zeros}1e-1075")));
        assert!(literal_open(&format!("16777217.{zeros}f")));
        assert!(!literal_open(&format!("16777217.{zeros}1f")));
    }
}
