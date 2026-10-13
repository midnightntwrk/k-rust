use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::*;
use crate::builtin::hook_models::float::round_exact;

fn canonical(token: &str) -> String {
    canonical_float_text(token).unwrap_or_else(|refusal| panic!("{token}: {refusal:?}"))
}

/// The general rounding of `body` at `precision` and `exponent_bits`, also for binary32 and
/// binary64, which `canonical_float_text` writes through the hooks' writers instead.
fn general(body: &str, precision: u64, exponent_bits: u64) -> Result<String, FloatTextRefusal> {
    let (negative, magnitude) = Magnitude::parse(body);
    Other {
        negative,
        magnitude,
        precision: BigUint::from(precision),
        exponent_bits: BigUint::from(exponent_bits),
        _body: body,
    }
    .plan()?
    .text()
}

/// The exact value of a canonical text: `None` for NaN and the infinities, otherwise the sign and
/// `num/den`.
fn decoded(text: &str) -> Option<(bool, BigUint, BigUint)> {
    let body = &text[..text.rfind('p').expect("a suffix")];
    let (negative, body) = match body.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, body),
    };
    if body == "NaN" || body == "Infinity" {
        return None;
    }
    let (digits, exponent) = body.split_once('e').expect("an exponent");
    let digits: BigUint = digits.parse().unwrap();
    let exponent: i64 = exponent.parse().unwrap();
    let power = BigUint::from(10_u8).pow(exponent.unsigned_abs() as u32);
    Some(if exponent < 0 {
        (negative, digits, power)
    } else {
        (negative, digits * power, BigUint::one())
    })
}

/// The exact decimal literal of `±mantissa * 2^exponent` in the format `pNxM`.
fn literal(negative: bool, mantissa: &BigUint, exponent: i64, format: (u64, u64)) -> String {
    let sign = if negative { "-" } else { "" };
    let digits = if exponent < 0 {
        format!(
            "{}e{exponent}",
            mantissa * BigUint::from(5_u8).pow(exponent.unsigned_abs() as u32)
        )
    } else {
        format!("{}e0", mantissa << exponent as u64)
    };
    format!("{sign}{digits}p{}x{}", format.0, format.1)
}

/// `literal` moved by `±10^-k` relative to its last digit: the text with `k` more digits, plus or
/// minus one unit of the last.
fn nudged(literal: &str, k: u32, up: bool) -> String {
    let (body, suffix) = literal.split_at(literal.rfind('p').unwrap());
    let (sign, body) = match body.strip_prefix('-') {
        Some(rest) => ("-", rest),
        None => ("", body),
    };
    let (digits, exponent) = body.split_once('e').unwrap();
    let digits: BigUint = digits.parse::<BigUint>().unwrap() * BigUint::from(10_u8).pow(k);
    let digits = if up { digits + 1_u8 } else { digits - 1_u8 };
    let exponent = exponent.parse::<i64>().unwrap() - i64::from(k);
    format!("{sign}{digits}e{exponent}{suffix}")
}

/// Deterministic literals at the edges where rounding bugs live, for the format `(N, M)`: exact
/// midpoints between neighbours and the midpoints moved by `±10^-k`, `max + 1/2 ulp` (ties to
/// infinity), half the least subnormal (ties to zero) and just above it, the largest subnormal
/// plus half an ulp (the least normal), an all-ones significand plus half an ulp (carries into
/// the next binade), and the negation of each.
pub(in crate::builtin) fn boundary_literals(format: (u64, u64)) -> Vec<String> {
    let (n, m) = (format.0 as i64, format.1 as i64);
    let emax = (1_i64 << (m - 1)) - 1;
    let emin = 1 - emax;
    let one = BigUint::one();
    let all_ones = |bits: i64| (BigUint::one() << bits as u64) - 1_u8;
    let mut positive = vec![
        // max + 1/2 ulp: (2^(N+1) - 1) * 2^(emax - N)
        literal(false, &all_ones(n + 1), emax - n, format),
        // half the least subnormal, 2^(emin - N)
        literal(false, &one, emin - n, format),
        // the largest subnormal plus half an ulp: (2^N - 1) * 2^(emin - N)
        literal(false, &all_ones(n), emin - n, format),
        // the least subnormal, the largest finite value, the least normal
        literal(false, &one, emin - n + 1, format),
        literal(false, &all_ones(n), emax - n + 1, format),
        literal(false, &one, emin, format),
    ];
    for binade in [emin, emin + 1, -1, 0, 1, n, emax - 1, emax] {
        // an all-ones significand plus half an ulp
        positive.push(literal(false, &all_ones(n + 1), binade - n, format));
        // midpoints of the binade's first, an even, an odd and its last significand
        for significand in [
            one.clone() << (n - 1) as u64,
            (one.clone() << (n - 1) as u64) + 2_u8,
            (one.clone() << (n - 1) as u64) + 1_u8,
            all_ones(n) - 1_u8,
        ] {
            let midpoint = (significand << 1) + 1_u8;
            positive.push(literal(false, &midpoint, binade - n, format));
        }
    }
    // subnormal midpoints
    for significand in [1_u8, 2, 3] {
        let midpoint = (BigUint::from(significand) << 1) + 1_u8;
        positive.push(literal(false, &midpoint, emin - n, format));
    }
    let mut literals = Vec::new();
    for literal in positive {
        for k in [1, 3] {
            literals.push(nudged(&literal, k, true));
            literals.push(nudged(&literal, k, false));
        }
        literals.push(format!("-{literal}"));
        literals.push(literal);
    }
    literals
}

/// A small deterministic generator of decimal literals of `format`: 1 to 25 digits and a decimal
/// exponent spread over the format's range and beyond it.
pub(in crate::builtin) fn random_literals(format: (u64, u64), count: usize) -> Vec<String> {
    let mut state = 0x9e37_79b9_7f4a_7c15_u64 ^ (format.0 << 32) ^ format.1;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let emax = (1_i64 << (format.1.min(20) - 1)) - 1;
    let reach = (emax as f64 * std::f64::consts::LOG10_2) as i64 + format.0 as i64 / 3 + 3;
    (0..count)
        .map(|_| {
            let length = 1 + next() % 25;
            let digits: String = (0..length)
                .map(|_| char::from(b'0' + (next() % 10) as u8))
                .collect();
            let exponent = (next() % (2 * reach as u64 + 1)) as i64 - reach;
            let sign = if next() % 2 == 0 { "" } else { "-" };
            format!("{sign}{digits}e{exponent}p{}x{}", format.0, format.1)
        })
        .collect()
}

/// The value the exact rounding model of the hook tests gives `literal` in `(N, M)`, as the
/// canonical text's decoded value would be: `None` for an infinity.
fn modelled(literal: &str, format: (u64, u64)) -> Option<(bool, BigUint, BigUint)> {
    let (negative, num, den) = decoded(literal).expect("finite");
    let emax = (1_i64 << (format.1 - 1)) - 1;
    let (mantissa, quantum) = round_exact(format.0 as i64, 1 - emax, emax, &num, &den)?;
    Some(if quantum < 0 {
        (negative, mantissa, BigUint::one() << quantum.unsigned_abs())
    } else {
        (negative, mantissa << quantum as u64, BigUint::one())
    })
}

fn same_value(left: &(bool, BigUint, BigUint), right: &(bool, BigUint, BigUint)) -> bool {
    left.0 == right.0 && &left.1 * &right.2 == &right.1 * &left.2
}

#[test]
fn every_binary64_spelling_of_two_is_one_text() {
    for token in [
        "2.0",
        "0.2e1",
        "2.0d",
        "2.0D",
        "2.0p53x11",
        "2.0p053x011",
        "2.00000000000000001",
        "+2",
        "2.",
    ] {
        assert_eq!(canonical(token), "2.0000000000000000e+00p53x11", "{token}");
    }
    for token in ["2.0f", "2.0F", "2.0p24x8", "2.0P024X08"] {
        assert_eq!(canonical(token), "2.00000000e+00p24x8", "{token}");
    }
}

#[test]
fn binary32_and_binary64_texts_are_the_texts_the_hooks_write() {
    for (token, expected) in [
        ("0.0", "0e+00p53x11"),
        ("-0.0", "-0e+00p53x11"),
        ("-0.0f", "-0e+00p24x8"),
        ("Infinity", "Infinityp53x11"),
        ("+Infinity", "Infinityp53x11"),
        ("-Infinityf", "-Infinityp24x8"),
        ("NaN", "NaNp53x11"),
        ("NaNd", "NaNp53x11"),
        ("NaNf", "NaNp24x8"),
        ("0.1", "1.0000000000000001e-01p53x11"),
        ("1e400", "Infinityp53x11"),
        ("-1e-400", "-0e+00p53x11"),
        ("1e-45f", "1.40129846e-45p24x8"),
    ] {
        assert_eq!(canonical(token), expected, "{token}");
        assert_eq!(canonical(expected), expected, "{expected} is a fixed point");
    }
}

#[test]
fn other_formats_are_rounded_and_written_as_exact_decimals() {
    for (token, expected) in [
        ("1.0p11x5", "1e0p11x5"),
        ("1.0001p11x5", "1e0p11x5"),
        ("1p11x5", "1e0p11x5"),
        ("100p11x5", "1e2p11x5"),
        // binary16's nearest value to 0.1 is 1638 * 2^-14
        ("0.1p11x5", "999755859375e-13p11x5"),
        // the least subnormal 2^-24 is the nearest to 6e-8
        ("6e-8p11x5", "59604644775390625e-24p11x5"),
        // the largest finite value is 65504; 65520 = max + 1/2 ulp ties to infinity
        ("65504p11x5", "65504e0p11x5"),
        ("65519.99p11x5", "65504e0p11x5"),
        ("65520p11x5", "Infinityp11x5"),
        ("70000p11x5", "Infinityp11x5"),
        ("-70000p11x5", "-Infinityp11x5"),
        // ties to even: 2049 lies between 2048 and 2050, 2051 between 2050 and 2052
        ("2049p11x5", "2048e0p11x5"),
        ("2051p11x5", "2052e0p11x5"),
        ("2049.0001p11x5", "205e1p11x5"),
        ("0.0p11x5", "0e0p11x5"),
        ("-0.0p11x5", "-0e0p11x5"),
        ("-1e-30p11x5", "-0e0p11x5"),
        // half the least subnormal ties to zero; just above it rounds to the least subnormal
        ("2.98023223876953125e-8p11x5", "0e0p11x5"),
        ("2.98023223876953126e-8p11x5", "59604644775390625e-24p11x5"),
        ("Infinityp11x5", "Infinityp11x5"),
        ("-Infinityp011x05", "-Infinityp11x5"),
        ("NaNp11x5", "NaNp11x5"),
        ("1.0p113x15", "1e0p113x15"),
        ("1.00p113x15", "1e0p113x15"),
        // N = 2, M = 2: the values 0, 0.5 (subnormal), 1, 1.5, 2, 3; emax = 1
        ("1.2p2x2", "1e0p2x2"),
        ("1.3p2x2", "15e-1p2x2"),
        ("2.5p2x2", "2e0p2x2"),
        ("3.4p2x2", "3e0p2x2"),
        ("3.5p2x2", "Infinityp2x2"),
        ("0.25p2x2", "0e0p2x2"),
        ("0.26p2x2", "5e-1p2x2"),
    ] {
        assert_eq!(canonical(token), expected, "{token}");
        assert_eq!(canonical(expected), expected, "{expected} is a fixed point");
    }
    assert_ne!(canonical("0.0p11x5"), canonical("-0.0p11x5"));
    assert_ne!(canonical("0.5p11x5"), canonical("0.5"));
}

/// A value exactly representable with a short significand is written without arithmetic on the
/// precision, however large it is; a value that needs rounding at that precision writes about
/// `N` bits, beyond the bound.
#[test]
fn a_huge_precision_is_computed_only_for_values_it_represents_exactly() {
    assert_eq!(canonical("1.0p99999999999x8"), "1e0p99999999999x8");
    assert_eq!(canonical("0.5p99999999999x8"), "5e-1p99999999999x8");
    assert!(float_canonical_bits_estimate("1.0p99999999999x8").unwrap() <= 64);
    assert!(canonical_float_text("1.0p53x99999999999").is_ok());
    for token in ["0.1p99999999999x8", "1e-1000000p53x32", "1e1000000p53x32"] {
        let refusal = canonical_float_text(token).expect_err(token);
        let FloatTextRefusal::BeyondBound { estimate_bits } = refusal else {
            panic!("{token}: {refusal:?}");
        };
        assert!(estimate_bits > MAX_FLOAT_CANONICAL_BITS, "{token}");
        assert_eq!(
            float_canonical_bits_estimate(token),
            Err(refusal),
            "{token}"
        );
        assert!(!refusal.names_no_element());
    }
    // In range at an exponent field this wide, so the exact decimal would be far beyond the
    // bound even at 11 bits.
    assert!(matches!(
        canonical_float_text("1e-1000000p11x99999999999"),
        Err(FloatTextRefusal::BeyondBound { .. })
    ));
    // Decided by exponent bounds alone, however long the exponent.
    assert_eq!(canonical("1e99999999999999999999p53x30"), "Infinityp53x30");
    assert_eq!(canonical("-1e-99999999999999999999p53x30"), "-0e0p53x30");
}

#[test]
fn fields_of_zero_name_no_format_and_fields_of_one_are_not_computed() {
    for token in ["1.0p0x11", "1.0p53x0", "1.0p00x11", "NaNp0x8"] {
        assert_eq!(
            canonical_float_text(token),
            Err(FloatTextRefusal::ZeroFormatField),
            "{token}"
        );
    }
    for token in ["1.0p1x8", "1.0p8x1", "NaNp1x1", "1.0p01x8"] {
        let refusal = canonical_float_text(token).expect_err(token);
        assert_eq!(refusal, FloatTextRefusal::UncomputedFormat, "{token}");
        assert!(!refusal.names_no_element());
    }
    for token in ["inf", "-.5", " 1.0", "1.0p", "1.0x8", "", "1e"] {
        assert_eq!(
            canonical_float_text(token),
            Err(FloatTextRefusal::NotALiteral),
            "{token:?}"
        );
    }
}

/// The general rounding agrees with Rust's correctly rounded parse at binary32 and binary64 on
/// boundary and random literals.
#[test]
fn the_general_rounding_agrees_with_the_native_formats() {
    for format in [(24, 8), (53, 11)] {
        let mut literals = boundary_literals(format);
        literals.extend(random_literals(format, 2000));
        for token in literals {
            let body = &token[..token.rfind('p').unwrap()];
            let native = if format.0 == 24 {
                body.parse::<f32>().map(f64::from).unwrap()
            } else {
                body.parse::<f64>().unwrap()
            };
            let text = general(body, format.0, format.1).unwrap();
            match decoded(&text) {
                None => {
                    assert!(native.is_infinite(), "{token}: {text} for {native:e}");
                    assert_eq!(text.starts_with('-'), native < 0.0, "{token}: {text}");
                }
                Some((negative, num, den)) => {
                    assert_eq!(negative, native.is_sign_negative(), "{token}: {text}");
                    let expected = decoded(&format!(
                        "{}p{}x{}",
                        exact_of_f64(native.abs()),
                        format.0,
                        format.1
                    ))
                    .unwrap();
                    assert_eq!(
                        &num * &expected.2,
                        &expected.1 * &den,
                        "{token}: {text} for {native:e}"
                    );
                }
            }
        }
    }
}

/// The exact decimal `DeQ` of a finite nonnegative binary64.
fn exact_of_f64(value: f64) -> String {
    if value == 0.0 {
        return "0e0".into();
    }
    let bits = value.to_bits();
    let field = ((bits >> 52) & 0x7ff) as i64;
    let fraction = bits & ((1 << 52) - 1);
    let (mantissa, exponent) = if field == 0 {
        (fraction, -1074)
    } else {
        (fraction | 1 << 52, field - 1075)
    };
    let text = literal(false, &BigUint::from(mantissa), exponent, (0, 0));
    text[..text.rfind('p').unwrap()].to_owned()
}

/// The canonical text agrees with the exact rational rounding of the hook models for formats of
/// at most 53 bits, on boundary and random literals.
#[test]
fn the_canonical_text_agrees_with_the_exact_rounding_model() {
    for format in [
        (2, 2),
        (2, 3),
        (3, 2),
        (4, 3),
        (5, 4),
        (8, 8),
        (11, 5),
        (24, 8),
        (30, 9),
        (53, 11),
    ] {
        let mut literals = boundary_literals(format);
        literals.extend(random_literals(format, 600));
        for token in literals {
            let text = general(&token[..token.rfind('p').unwrap()], format.0, format.1).unwrap();
            let expected = modelled(&token, format);
            match (decoded(&text), expected) {
                (None, None) => {}
                (Some(actual), Some(expected)) => assert!(
                    same_value(&actual, &expected)
                        || (actual.1.is_zero() && expected.1.is_zero() && actual.0 == expected.0),
                    "{token}: {text} against {expected:?}"
                ),
                (actual, expected) => panic!("{token}: {text} ({actual:?}) against {expected:?}"),
            }
            assert_eq!(
                general(&text[..text.rfind('p').unwrap()], format.0, format.1).as_ref(),
                Ok(&text),
                "{text} is a fixed point"
            );
        }
    }
}

#[test]
fn the_canonical_text_of_a_canonical_text_is_itself() {
    for format in [(11, 5), (113, 15), (64, 15), (200, 16)] {
        for token in random_literals(format, 200) {
            let Ok(text) = canonical_float_text(&token) else {
                continue;
            };
            assert_eq!(canonical(&text), text, "{token}");
        }
    }
}

/// The very long exact decimals within the bound are written: the least subnormal of p113x15 is
/// `5^16494 * 10^-16494`, 11,529 digits.
#[test]
fn the_least_subnormal_of_a_wide_format_is_written_exactly() {
    let least = literal(false, &BigUint::one(), -16494, (113, 15));
    let text = canonical(&least);
    let digits = &text[..text.find('e').unwrap()];
    assert_eq!(digits.len(), 11529);
    assert_eq!(text, least);
    let half = literal(false, &BigUint::one(), -16495, (113, 15));
    assert_eq!(canonical(&half), "0e0p113x15");
    assert_eq!(canonical(&nudged(&half, 2, true)), least);
}

#[test]
fn scaled_logarithms_bracket_their_products() {
    for x in [-1_000_000_007_i64, -3, -1, 0, 1, 2, 7, 1_000_000_007] {
        let x = BigInt::from(x);
        let exact = x.to_f64().unwrap() * std::f64::consts::LOG2_10;
        assert!(scale_floor(&x, LOG2_10).to_f64().unwrap() <= exact + 1e-6);
        assert!(scale_ceil(&x, LOG2_10).to_f64().unwrap() >= exact - 1e-6);
        assert!(scale_ceil(&x, LOG2_10) >= scale_floor(&x, LOG2_10));
    }
    assert_eq!(floor_div(&BigInt::from(-7), 2), BigInt::from(-4));
    assert!(floor_div(&BigInt::from(7), 2).is_positive());
}

/// Whatever load accepts, its canonical text is accepted too and is its own canonical text, at
/// the bound as well: the first 94,700 digits of the exact decimal of the largest subnormal of
/// p314223x12 round to that subnormal, whose exact decimal has a significand of 1,048,574 bits,
/// two bits within `MAX_FLOAT_CANONICAL_BITS`; so do the neighbouring formats, whatever their
/// outcome.
#[test]
fn every_accepted_literal_has_an_accepted_canonical_text_at_the_bound() {
    for precision in [314_222_u64, 314_223, 314_224] {
        let format = (precision, 12);
        let emin = 1 - ((1_i64 << 11) - 1);
        let largest_subnormal = literal(
            false,
            &((BigUint::one() << (precision - 1)) - 1_u8),
            emin - precision as i64 + 1,
            format,
        );
        let (body, suffix) = largest_subnormal.split_at(largest_subnormal.rfind('p').unwrap());
        let (digits, exponent) = body.split_once('e').unwrap();
        let kept = 94_700;
        let shortened = format!(
            "{}e{}{suffix}",
            &digits[..kept],
            exponent.parse::<i64>().unwrap() + (digits.len() - kept) as i64
        );
        for token in [largest_subnormal.as_str(), shortened.as_str()] {
            let Ok(text) = canonical_float_text(token) else {
                continue;
            };
            assert_eq!(
                canonical_float_text(&text).as_ref(),
                Ok(&text),
                "p{precision}x12: the canonical text of a {}-character literal",
                token.len()
            );
        }
        if precision == 314_223 {
            assert_eq!(canonical(&shortened), largest_subnormal);
        }
    }
}

/// An exponent of more than twenty digits is decided from its length and sign, without parsing
/// it: a ten-million-digit exponent gives the infinity or the zero of a format whose exponent
/// field is at most 64 bits, and is refused otherwise, as is a tiny value within the subnormal
/// range of a huge precision.
#[test]
fn a_remote_exponent_is_decided_from_its_length() {
    let nines = "9".repeat(10_000_000);
    let started = std::time::Instant::now();
    assert_eq!(canonical(&format!("1e{nines}p11x5")), "Infinityp11x5");
    assert_eq!(
        canonical(&format!("-1.5e+{nines}p53x64")),
        "-Infinityp53x64"
    );
    assert_eq!(canonical(&format!("-1e-{nines}p113x15")), "-0e0p113x15");
    assert_eq!(canonical(&format!("0e{nines}p11x5")), "0e0p11x5");
    for token in [
        format!("1e{nines}p53x65"),
        format!("1e-{nines}p53x65"),
        // 10^-(10^24) lies within the subnormal range of a precision of 10^40 - 1 bits.
        format!("1e-0001{}p{}x8", "0".repeat(24), "9".repeat(40)),
    ] {
        assert!(
            matches!(
                canonical_float_text(&token),
                Err(FloatTextRefusal::BeyondBound { .. })
            ),
            "{}",
            &token[token.rfind('p').unwrap()..]
        );
    }
    // Below the least subnormal of that format, however wide.
    assert_eq!(
        canonical(&format!("1e-{nines}p{}x8", "9".repeat(40))),
        format!("0e0p{}x8", "9".repeat(40))
    );
    // Twenty digits are still parsed, and decided by the exponent bracket.
    assert_eq!(canonical("1e-99999999999999999999p11x5"), "0e0p11x5");
    // Parsing a ten-million-digit exponent takes minutes; deciding it is linear.
    assert!(started.elapsed() < std::time::Duration::from_secs(60));
}
