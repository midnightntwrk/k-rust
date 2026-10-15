//! An independent oracle for the canonical text of a Float literal: MPFR's value of the literal
//! in its format. Built only with the test feature `mpfr-oracle`, which links MPFR through `rug`
//! (CI enables it); no other build of the backend depends on MPFR.
//!
//! A literal of the format `pNxM` denotes its decimal rounded to nearest, ties to even, at `N`
//! bits of precision and then into the format's exponent range with subnormals, as IEEE 754
//! rounds (`domains.md`). MPFR computes that value correctly rounded at any precision, with the
//! range and subnormals imposed from the rounding direction (`clamp_exp`, `subnormalize_round`).
//! The backend's canonicalizer (`canonical_float_text`) is an implementation of its own, in
//! exact rational arithmetic, so a difference between the value its text denotes and MPFR's is a
//! defect on one side.

use std::str::FromStr;

use num_bigint::BigInt;
use rug::{
    Float,
    float::{self, Round, Special},
};

use crate::builtin::{
    FloatTextRefusal, MAX_FLOAT_CANONICAL_BITS, canonical_float_text, float_canonical_bits_estimate,
};

/// The precision and exponent-bits fields and the value text of a Float literal.
fn parts(literal: &str) -> (&str, u32, u32) {
    if let Some((value_and_precision, exponent)) = literal.rsplit_once(['x', 'X'])
        && let Some((value, precision)) = value_and_precision.rsplit_once(['p', 'P'])
    {
        return (value, precision.parse().unwrap(), exponent.parse().unwrap());
    }
    match literal.strip_suffix(['f', 'F']) {
        Some(value) => (value, 24, 8),
        None => (literal.strip_suffix(['d', 'D']).unwrap_or(literal), 53, 11),
    }
}

/// MPFR's value of the literal `literal` in its format: the decimal rounded to nearest at the
/// format's precision, then into its exponent range with subnormals. The exponents are MPFR's,
/// of a significand in `[1/2, 1)`: the largest finite value has exponent `2^(M-1)`, the least
/// normal one `3 - 2^(M-1)`, and the least subnormal `3 - 2^(M-1) - (N - 1)`.
fn mpfr_value(literal: &str) -> Float {
    let (text, precision, exponent_bits) = parts(literal);
    let special = |special| Float::with_val(precision, special);
    match text {
        "Infinity" | "+Infinity" => return special(Special::Infinity),
        "-Infinity" => return special(Special::NegInfinity),
        "NaN" => return special(Special::Nan),
        _ => {}
    }
    let maximum = 1i32 << (exponent_bits - 1);
    let normal_minimum = 1 - maximum + 2;
    let subnormal_minimum = normal_minimum - (precision as i32 - 1);
    assert!(
        subnormal_minimum >= float::exp_min() && maximum <= float::exp_max(),
        "{literal}: the format is outside MPFR's exponent range"
    );
    let parsed = Float::parse(text).unwrap();
    let (mut value, direction) = Float::with_val_round(precision, parsed, Round::Nearest);
    let direction = value
        .clamp_exp(direction, Round::Nearest, subnormal_minimum, maximum)
        .unwrap();
    value.subnormalize_round(normal_minimum, direction, Round::Nearest);
    value
}

/// `(mantissa, exponent)` with `value = mantissa * 2^exponent`, for a finite `value`.
fn integer_exponent(value: &Float) -> (BigInt, i32) {
    value
        .to_integer_exp()
        .map(|(mantissa, exponent)| (BigInt::from_str(&mantissa.to_string()).unwrap(), exponent))
        .unwrap_or((BigInt::from(0), 0))
}

/// The exact decimal literal of `±mantissa * 2^exponent` in the format `pNxM`.
fn exact_literal(negative: bool, mantissa: &BigInt, exponent: i64, format: (u32, u32)) -> String {
    let sign = if negative { "-" } else { "" };
    let digits = if exponent < 0 {
        format!(
            "{}e{exponent}",
            mantissa * BigInt::from(5).pow(exponent.unsigned_abs() as u32)
        )
    } else {
        format!("{}e0", mantissa << exponent as u64)
    };
    format!("{sign}{digits}p{}x{}", format.0, format.1)
}

/// `literal` with `k` more digits, plus or minus one unit of the last.
fn nudged(literal: &str, k: u32, up: bool) -> String {
    let (body, suffix) = literal.split_at(literal.rfind('p').unwrap());
    let (digits, exponent) = body.split_once('e').unwrap();
    let digits = digits.parse::<BigInt>().unwrap() * BigInt::from(10).pow(k);
    let digits = if up { digits + 1 } else { digits - 1 };
    let exponent = exponent.parse::<i64>().unwrap() - i64::from(k);
    format!("{digits}e{exponent}{suffix}")
}

/// Deterministic literals where rounding bugs live, for the format `(N, M)`: `max + 1/2 ulp`
/// (ties to infinity), half the least subnormal (ties to zero), the largest subnormal plus half
/// an ulp (the least normal), an all-ones significand plus half an ulp (carries into the next
/// binade), exact midpoints between neighbours, each moved by `±10^-k`, and negated.
fn boundary_literals(format: (u32, u32)) -> Vec<String> {
    let (n, m) = (i64::from(format.0), i64::from(format.1));
    let emax = (1_i64 << (m - 1)) - 1;
    let emin = 1 - emax;
    let ones = |bits: i64| (BigInt::from(1) << bits as u64) - 1;
    let one = BigInt::from(1);
    let mut positive = vec![
        exact_literal(false, &ones(n + 1), emax - n, format),
        exact_literal(false, &one, emin - n, format),
        exact_literal(false, &ones(n), emin - n, format),
        exact_literal(false, &one, emin - n + 1, format),
        exact_literal(false, &ones(n), emax - n + 1, format),
    ];
    for binade in [emin, emin + 1, -1, 0, 1, emax - 1, emax] {
        positive.push(exact_literal(false, &ones(n + 1), binade - n, format));
        for significand in [
            one.clone() << (n - 1) as u64,
            (one.clone() << (n - 1) as u64) + 1,
            (one.clone() << (n - 1) as u64) + 2,
            ones(n) - 1,
        ] {
            positive.push(exact_literal(
                false,
                &((significand << 1) + 1),
                binade - n,
                format,
            ));
        }
    }
    for midpoint in [3, 5, 7] {
        positive.push(exact_literal(
            false,
            &BigInt::from(midpoint),
            emin - n,
            format,
        ));
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

/// Deterministic decimal literals of 1 to 25 digits with exponents across the format's range.
fn random_literals(format: (u32, u32), count: usize) -> Vec<String> {
    let mut state = 0x2545_f491_4f6c_dd1d_u64 ^ (u64::from(format.0) << 32) ^ u64::from(format.1);
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let emax = (1_i64 << (format.1 - 1)) - 1;
    let reach = (emax as f64 * std::f64::consts::LOG10_2) as i64 + i64::from(format.0) / 3 + 3;
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

/// `(negative, num, den)` of a finite canonical text `[-]DeQpNxM` of a format other than binary32
/// and binary64, whose decimal is exact.
fn denoted(text: &str) -> (bool, BigInt, BigInt) {
    let body = &text[..text.rfind('p').unwrap()];
    let (negative, body) = match body.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, body),
    };
    let (digits, exponent) = body.split_once(['e', 'E']).unwrap();
    let digits: BigInt = digits.replace('.', "").parse().unwrap();
    let fraction = body.split_once('.').map_or(0, |(_, rest)| {
        rest.split_once(['e', 'E'])
            .map_or(rest.len(), |(fraction, _)| fraction.len())
    });
    let exponent = exponent.parse::<i64>().unwrap() - fraction as i64;
    let power = BigInt::from(10).pow(exponent.unsigned_abs() as u32);
    if exponent < 0 {
        (negative, digits, power)
    } else {
        (negative, digits * power, BigInt::from(1))
    }
}

/// The backend's canonical text of a Float literal, built at load and by `String2Float` for
/// every format, denotes exactly MPFR's value of the literal, NaN and the infinities included.
/// Literals the backend refuses for its size bound are excluded, and the refusal agrees with its
/// estimate.
#[test]
fn the_backend_canonical_float_text_agrees_with_mpfr() {
    let formats = [
        ((2, 2), 200),
        ((3, 3), 200),
        ((5, 4), 200),
        ((11, 5), 600),
        ((24, 8), 600),
        ((53, 11), 600),
        ((64, 15), 300),
        ((113, 15), 300),
        ((237, 17), 60),
    ];
    let cases = formats
        .iter()
        .flat_map(|&(format, random)| {
            let mut literals = boundary_literals(format);
            literals.extend(random_literals(format, random));
            literals.into_iter().map(move |literal| (format, literal))
        })
        .collect::<Vec<_>>();
    // The canonicalizer runs on a worker thread, and each literal gets a time limit, so a
    // canonicalizer that does not terminate on a literal fails the test on that literal instead
    // of stalling it.
    let (sender, receiver) = std::sync::mpsc::channel();
    let literals = cases
        .iter()
        .map(|(_, literal)| literal.clone())
        .collect::<Vec<_>>();
    std::thread::spawn(move || {
        for literal in literals {
            if sender.send(canonical_float_text(&literal)).is_err() {
                return;
            }
        }
    });
    let mut checked = 0;
    for (format, literal) in cases {
        let canonical = receiver
            .recv_timeout(std::time::Duration::from_secs(30))
            .unwrap_or_else(|_| panic!("the canonical text of {literal} took over 30 s"));
        let text = match canonical {
            Ok(text) => text,
            Err(refusal @ FloatTextRefusal::BeyondBound { estimate_bits }) => {
                assert!(estimate_bits > MAX_FLOAT_CANONICAL_BITS, "{literal}");
                assert_eq!(float_canonical_bits_estimate(&literal), Err(refusal));
                continue;
            }
            Err(refusal) => panic!("{literal}: {refusal:?}"),
        };
        let value = mpfr_value(&literal);
        if value.is_nan() {
            assert!(text.starts_with("NaN"), "{literal}: {text}");
        } else if value.is_infinite() {
            assert_eq!(
                text,
                format!(
                    "{}Infinityp{}x{}",
                    if value.is_sign_negative() { "-" } else { "" },
                    format.0,
                    format.1
                ),
                "{literal}"
            );
        } else if matches!(format, (24, 8) | (53, 11)) {
            // binary32 and binary64 texts are the hooks' round-trip decimals, each a literal
            // of its format: MPFR's value of the text is MPFR's value of the literal.
            let read = mpfr_value(&text);
            assert_eq!(
                read.is_sign_negative(),
                value.is_sign_negative(),
                "{literal}: {text}"
            );
            assert_eq!(read, value, "{literal}: {text} against MPFR");
        } else {
            let (negative, num, den) = denoted(&text);
            assert_eq!(negative, value.is_sign_negative(), "{literal}: {text}");
            let (mantissa, exponent) = integer_exponent(&value);
            let mantissa = if negative { -mantissa } else { mantissa };
            // num / den = mantissa * 2^exponent
            let (left, right) = if exponent < 0 {
                (num << exponent.unsigned_abs() as u64, mantissa * den)
            } else {
                (num, (mantissa << exponent as u64) * den)
            };
            assert_eq!(left, right, "{literal}: {text} against MPFR");
        }
        checked += 1;
    }
    assert!(checked > 3000, "only {checked} literals were checked");
}
