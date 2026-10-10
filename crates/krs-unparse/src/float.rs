//! Float domain values as K's LLVM backend prints them.
//!
//! Every `krun` output of a result prints a Float as the LLVM runtime writes it, in MPFR's decimal
//! form: the significand's `1 + ceil(p log10 2)` correctly rounded digits after `0.`, the decimal
//! exponent, and the format suffix (none for binary64, `f` for binary32, `pPxE` otherwise), so
//! `1.5` prints as `0.15000000000000000e1` and `-0.0f` as `-0.000000000e0f`; infinities print as
//! `Infinity` and NaN as `NaN`, each with the suffix. `--output pretty`, `kast`, `kore`, and
//! `json` all carry that text. k-rust writes its own canonical token
//! (`1.5000000000000000e+00p53x11`), and a program literal keeps its text, so
//! [`crate::Unparser::llvm_floats`] rewrites every binary32 and binary64 Float of a result to the
//! LLVM form, and [`crate::Mode::Pretty`] prints through it. A Float of any other format is left
//! as it is.

use crate::data::PrintData;
use k_rust::kore::ast::{KoreString, Pattern, Sort};
use k_rust::kore::node::PatternSource;
use k_rust::kore::walk;

/// `pattern` with each binary32 and binary64 Float domain value in the LLVM runtime's printed
/// form, or `None` when no domain value changes.
pub(crate) fn llvm_floats(data: &PrintData, pattern: &Pattern) -> Option<Pattern> {
    let printed = |pattern: &Pattern| -> Option<KoreString> {
        let Pattern::DomainValue {
            sort: Sort::Application { name, .. },
            value,
        } = pattern
        else {
            return None;
        };
        if data
            .hooks
            .get(name)
            .is_none_or(|hook| hook != "FLOAT.Float")
        {
            return None;
        }
        let token = value.as_utf8().ok()?;
        let text = llvm_float_text(token)?;
        (text != token).then(|| KoreString::from_bytes(text.into_bytes()))
    };
    let mut changed = false;
    walk::for_each_post_order(pattern, |node| changed = changed || printed(node).is_some());
    changed.then(|| {
        walk::rebuild(pattern, |node, children| match (node, printed(node)) {
            (Pattern::DomainValue { sort, .. }, Some(value)) => Pattern::DomainValue {
                sort: sort.clone(),
                value,
            },
            _ => node.node().split().0.fill(children).into_pattern(),
        })
    })
}

/// The LLVM runtime's text of the K Float token `token`, when its format is
/// binary32 or binary64.
pub fn llvm_float_text(token: &str) -> Option<String> {
    let (value, precision, exponent_bits) = split_format(token)?;
    let (negative, kind) = match (precision, exponent_bits) {
        (24, 8) => classify(value.parse::<f32>().ok().map(f64::from), value)?,
        (53, 11) => classify(value.parse::<f64>().ok(), value)?,
        _ => return None,
    };
    let suffix = if precision == 24 { "f" } else { "" };
    let sign = if negative { "-" } else { "" };
    let digits = if precision == 24 { 9 } else { 17 };
    Some(match kind {
        Kind::NaN => format!("NaN{suffix}"),
        Kind::Infinite => format!("{sign}Infinity{suffix}"),
        Kind::Zero => format!("{sign}0.{}e0{suffix}", "0".repeat(digits)),
        Kind::Finite(magnitude) => {
            let scientific = if precision == 24 {
                // Narrowing is exact: the value was parsed as a binary32.
                #[expect(
                    clippy::cast_possible_truncation,
                    reason = "the magnitude is a binary32 value widened to f64"
                )]
                let narrow = magnitude as f32;
                format!("{narrow:.8e}")
            } else {
                format!("{magnitude:.16e}")
            };
            let (mantissa, exponent) = scientific.split_once('e')?;
            let exponent = exponent.parse::<i32>().ok()? + 1;
            format!("{sign}0.{}e{exponent}{suffix}", mantissa.replace('.', ""))
        }
    })
}

enum Kind {
    NaN,
    Infinite,
    Zero,
    Finite(f64),
}

fn classify(parsed: Option<f64>, text: &str) -> Option<(bool, Kind)> {
    let negative = text.starts_with('-');
    let unsigned = text.trim_start_matches(['-', '+']);
    if unsigned == "NaN" {
        return Some((false, Kind::NaN));
    }
    if unsigned == "Infinity" {
        return Some((negative, Kind::Infinite));
    }
    let value = parsed?;
    if value.is_nan() {
        return Some((false, Kind::NaN));
    }
    let kind = if value.is_infinite() {
        Kind::Infinite
    } else if value == 0.0 {
        Kind::Zero
    } else {
        Kind::Finite(value.abs())
    };
    Some((value.is_sign_negative(), kind))
}

/// The value text and format of a K Float token: `pPxE`, `f`/`F` (binary32),
/// `d`/`D` or no suffix (binary64).
fn split_format(token: &str) -> Option<(&str, u32, u32)> {
    if let Some(index) = token.rfind(['p', 'P']) {
        let (value, format) = (&token[..index], &token[index + 1..]);
        if let Some((precision, exponent_bits)) = format.split_once(['x', 'X']) {
            return Some((value, precision.parse().ok()?, exponent_bits.parse().ok()?));
        }
        return None;
    }
    // `Infinity` ends in `y`, so only a final `f`/`d` is a suffix.
    match token.as_bytes().last()? {
        b'f' | b'F' => Some((&token[..token.len() - 1], 24, 8)),
        b'd' | b'D' => Some((&token[..token.len() - 1], 53, 11)),
        _ => Some((token, 53, 11)),
    }
}

#[cfg(test)]
mod tests {
    use super::llvm_float_text;

    /// Each k-rust token or program literal, and `krun --output pretty` of
    /// the same value (K 7.1.337, LLVM backend).
    #[test]
    fn floats_print_as_the_llvm_runtime_prints_them() {
        for (token, printed) in [
            ("-1.5000000000000000e+00p53x11", "-0.15000000000000000e1"),
            ("1.5", "0.15000000000000000e1"),
            ("1.5p53x11", "0.15000000000000000e1"),
            ("0.15000000000000000e1", "0.15000000000000000e1"),
            ("-1.00000001e-01p24x8", "-0.100000001e0f"),
            ("0.1f", "0.100000001e0f"),
            ("-Infinityp24x8", "-Infinityf"),
            ("Infinityp53x11", "Infinity"),
            ("NaNp53x11", "NaN"),
            ("NaNp24x8", "NaNf"),
            ("-0e+00p53x11", "-0.00000000000000000e0"),
            ("1.0000000000000000e+308p53x11", "0.10000000000000000e309"),
            (
                "-2.5000000000000171e-310p53x11",
                "-0.25000000000000171e-309",
            ),
        ] {
            assert_eq!(llvm_float_text(token).as_deref(), Some(printed), "{token}");
        }
    }

    #[test]
    fn other_formats_are_left_alone() {
        assert_eq!(llvm_float_text("0.5p113x15"), None);
        assert_eq!(llvm_float_text("not-a-float"), None);
    }
}
