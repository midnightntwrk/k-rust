//! ```toml algorithm-site
//! id = "kompile.constant_folding.evaluate"
//! role = "part"
//! sites = ["evaluate", "KFloat::parse"]
//! ```
//!
//! This helper module evaluates the FLOAT hooks of kompile.constant_folding.evaluate.
//! Its cost is measured by the constant folding `--timings` phase; it bumps no counter.
//!
//! MPFR-backed implementation of K's `FLOAT` constant-folding hooks.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    cmp::Ordering,
    ffi::{CStr, CString, c_long},
    ptr,
    str::FromStr,
};

use gmp_mpfr_sys::mpfr;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use rug::{
    Float, Integer,
    float::{self, Round, Special},
    ops::Pow,
};

use super::{MAX_FOLDED_BITS, Unfolded, Value, int_value, string_value, too_large};

#[derive(Clone, Debug)]
pub(super) struct KFloat {
    value: Float,
    exponent_bits: u32,
}

impl KFloat {
    pub(super) fn parse(token: &str) -> Result<Self, Unfolded> {
        if !k_rust_backend::builtin::is_float_syntax(token) {
            return Err(format!("invalid Float token {token:?}").into());
        }
        let (text, precision, exponent_bits) = parse_parts(token)?;
        validate_context(precision, exponent_bits)
            .map_err(|_| format!("invalid Float token {token:?}"))?;
        check_precision(precision)?;
        match text {
            "Infinity" => Ok(Self::special(precision, exponent_bits, Special::Infinity)),
            "-Infinity" => Ok(Self::special(
                precision,
                exponent_bits,
                Special::NegInfinity,
            )),
            "+Infinity" => Ok(Self::special(precision, exponent_bits, Special::Infinity)),
            "NaN" => Ok(Self::special(precision, exponent_bits, Special::Nan)),
            text => {
                let parsed =
                    Float::parse(text).map_err(|_| format!("invalid Float token {token:?}"))?;
                let (value, direction) = Float::with_val_round(precision, parsed, Round::Nearest);
                Self::from_rounded(value, exponent_bits, direction)
            }
        }
    }

    /// The size of the value in the unit of `MAX_FOLDED_BITS`: its precision.
    pub(super) fn bits(&self) -> u64 {
        u64::from(self.value.prec())
    }

    /// [`Self::try_token`] for a value the test knows to be writable.
    #[cfg(test)]
    pub(super) fn token(&self) -> String {
        self.try_token()
            .expect("the test's Float value has a token within the bound")
    }

    /// The token of the value: its decimal at the precision's round-trip length, with the
    /// precision and exponent-width suffix. A token whose text would exceed `MAX_FOLDED_BITS`
    /// (a finite value of precision above about 435,000 bits) is `TooLarge`, so the fold leaves
    /// the application as written; the length is decided from the precision before MPFR formats
    /// anything.
    pub(super) fn try_token(&self) -> Result<String, Unfolded> {
        let value = if self.value.is_nan() {
            "NaN".into()
        } else if self.value.is_infinite() {
            if self.value.is_sign_negative() {
                "-Infinity"
            } else {
                "Infinity"
            }
            .into()
        } else if self.value.is_zero() {
            if self.value.is_sign_negative() {
                "-0e+00"
            } else {
                "0e+00"
            }
            .into()
        } else {
            // `%Re` writes at least `ceil(p * log10(2))` significant digits at precision `p`,
            // the length that reads back as the same value.
            let digits = u64::from(self.value.prec()) * 30_103 / 100_000;
            if digits.saturating_mul(8) > MAX_FOLDED_BITS {
                return Err(too_large("FLOAT", digits * 8));
            }
            self.format("%Re")?
        };
        Ok(format!(
            "{value}p{}x{}",
            self.value.prec(),
            self.exponent_bits
        ))
    }

    fn format(&self, format: &str) -> Result<String, Unfolded> {
        if self.value.is_nan() {
            return Ok("NaN".into());
        }
        if self.value.is_infinite() {
            return Ok(if self.value.is_sign_negative() {
                "-Infinity"
            } else {
                "Infinity"
            }
            .into());
        }
        validate_mpfr_format(format)?;
        let format = CString::new(format)
            .map_err(|_| "Float format contains an embedded NUL byte".to_owned())?;
        // SAFETY: `validate_mpfr_format` permits at most one consuming conversion, requires it
        // to be an MPFR `R` conversion, and rejects dynamic widths. `format` is NUL-terminated,
        // `self.value.as_raw()` has the exact `mpfr_t` type expected by the variadic function,
        // and the second call receives the capacity reported by the first call plus its NUL.
        unsafe {
            let length = mpfr::snprintf(ptr::null_mut(), 0, format.as_ptr(), self.value.as_raw());
            if length < 0 {
                return Err("invalid MPFR Float format".into());
            }
            if (length as u64).saturating_mul(8) > MAX_FOLDED_BITS {
                return Err(too_large("STRING.floatFormat", (length as u64) * 8));
            }
            let mut buffer = vec![0u8; length as usize + 1];
            let written = mpfr::snprintf(
                buffer.as_mut_ptr().cast(),
                buffer.len(),
                format.as_ptr(),
                self.value.as_raw(),
            );
            if written < 0 || written != length {
                return Err("MPFR could not format the Float consistently".into());
            }
            Ok(CStr::from_bytes_with_nul(&buffer)
                .map_err(|error| error.to_string())?
                .to_str()
                .map(str::to_owned)
                .map_err(|error| error.to_string())?)
        }
    }

    /// Whether `other` has this value's precision and exponent width, so that a binary
    /// operation over the two has their format as its destination. Over two formats
    /// `domains.md` names no destination: the result format is a reading k-rust applies only in
    /// an execution, while the fold's output is the definition that proofs load too, so such a
    /// pair is left unfolded as a value the definition leaves open (`Unspecified`).
    fn context_matches(&self, other: &Self, hook: &str) -> Result<(), Unfolded> {
        if self.value.prec() == other.value.prec() && self.exponent_bits == other.exponent_bits {
            Ok(())
        } else {
            Err(Unfolded::Unspecified(format!(
                "Arguments to hook {hook} have two formats, whose result format is chosen only in \
                 an execution."
            )))
        }
    }

    fn special(precision: u32, exponent_bits: u32, special: Special) -> Self {
        Self {
            value: Float::with_val(precision, special),
            exponent_bits,
        }
    }

    fn from_rounded(
        mut value: Float,
        exponent_bits: u32,
        direction: Ordering,
    ) -> Result<Self, Unfolded> {
        limit_exponent(&mut value, exponent_bits, direction)?;
        Ok(Self {
            value,
            exponent_bits,
        })
    }

    fn exact(&self, operation: impl FnOnce(Float) -> Float) -> Self {
        Self {
            value: operation(self.value.clone()),
            exponent_bits: self.exponent_bits,
        }
    }

    fn unary_round(
        &self,
        operation: impl FnOnce(&mut Float) -> Ordering,
    ) -> Result<Self, Unfolded> {
        let mut value = self.value.clone();
        let direction = operation(&mut value);
        Self::from_rounded(value, self.exponent_bits, direction)
    }

    fn binary(
        &self,
        other: &Self,
        hook: &str,
        operation: impl FnOnce(&Float, &Float) -> (Float, Ordering),
    ) -> Result<Self, Unfolded> {
        self.context_matches(other, hook)?;
        let (value, direction) = operation(&self.value, &other.value);
        Self::from_rounded(value, self.exponent_bits, direction)
    }
}

pub(super) fn evaluate(hook: &str, values: &[Value]) -> Option<Result<Value, Unfolded>> {
    match hook {
        "STRING.float2string" => unary_float(values, |a| a.try_token().map(Value::String)),
        "STRING.floatFormat" => float_format(values),
        "STRING.string2float" => match values {
            [value] => Some(
                string_value(value)
                    .and_then(KFloat::parse)
                    .map(Value::Float),
            ),
            _ => Some(Err(Unfolded::Unsupported(
                "constant-folding hook expected one argument".into(),
            ))),
        },
        "FLOAT.precision" => unary_float(values, |a| Ok(Value::Int(a.value.prec().into()))),
        "FLOAT.exponentBits" => unary_float(values, |a| Ok(Value::Int(a.exponent_bits.into()))),
        "FLOAT.exponent" => unary_float(values, |a| {
            let (minimum, maximum) = exponent_limits(a.exponent_bits)?;
            let exponent = if a.value.is_zero() {
                minimum
            } else if !a.value.is_finite() {
                maximum
            } else {
                let mpfr_exponent = a.value.get_exp().unwrap_or(minimum);
                if mpfr_exponent < minimum + 2 {
                    minimum
                } else {
                    mpfr_exponent - 1
                }
            };
            Ok(Value::Int(exponent.into()))
        }),
        "FLOAT.sign" => unary_float(values, |a| Ok(Value::Bool(a.value.is_sign_negative()))),
        "FLOAT.isNaN" => unary_float(values, |a| Ok(Value::Bool(a.value.is_nan()))),
        "FLOAT.neg" => unary_float(values, |a| Ok(Value::Float(a.exact(|value| -value)))),
        "FLOAT.abs" => unary_float(values, |a| Ok(Value::Float(a.exact(Float::abs)))),
        "FLOAT.floor" => unary_float(values, |a| Ok(Value::Float(a.exact(Float::floor)))),
        "FLOAT.ceil" => unary_float(values, |a| Ok(Value::Float(a.exact(Float::ceil)))),
        "FLOAT.trunc" => unary_float(values, |a| Ok(Value::Float(a.exact(Float::trunc)))),
        "FLOAT.exp" => unary_float(values, |a| {
            a.unary_round(|value| value.exp_round(Round::Nearest))
                .map(Value::Float)
        }),
        "FLOAT.log" => unary_float(values, |a| {
            a.unary_round(|value| value.ln_round(Round::Nearest))
                .map(Value::Float)
        }),
        "FLOAT.sin" => unary_float(values, |a| {
            a.unary_round(|value| value.sin_round(Round::Nearest))
                .map(Value::Float)
        }),
        "FLOAT.cos" => unary_float(values, |a| {
            a.unary_round(|value| value.cos_round(Round::Nearest))
                .map(Value::Float)
        }),
        "FLOAT.tan" => unary_float(values, |a| {
            a.unary_round(|value| value.tan_round(Round::Nearest))
                .map(Value::Float)
        }),
        "FLOAT.asin" => unary_float(values, |a| {
            a.unary_round(|value| value.asin_round(Round::Nearest))
                .map(Value::Float)
        }),
        "FLOAT.acos" => unary_float(values, |a| {
            a.unary_round(|value| value.acos_round(Round::Nearest))
                .map(Value::Float)
        }),
        "FLOAT.atan" => unary_float(values, |a| {
            a.unary_round(|value| value.atan_round(Round::Nearest))
                .map(Value::Float)
        }),
        "FLOAT.add" => binary_float(values, hook, |a, b| {
            Float::with_val_round(a.prec(), a + b, Round::Nearest)
        }),
        "FLOAT.sub" => binary_float(values, hook, |a, b| {
            Float::with_val_round(a.prec(), a - b, Round::Nearest)
        }),
        "FLOAT.mul" => binary_float(values, hook, |a, b| {
            Float::with_val_round(a.prec(), a * b, Round::Nearest)
        }),
        "FLOAT.div" => binary_float(values, hook, |a, b| {
            Float::with_val_round(a.prec(), a / b, Round::Nearest)
        }),
        "FLOAT.rem" => binary_float(values, hook, |a, b| {
            let mut value = a.clone();
            let direction = value.remainder_round(b, Round::Nearest);
            (value, direction)
        }),
        "FLOAT.pow" => binary_float(values, hook, |a, b| {
            Float::with_val_round(a.prec(), a.clone().pow(b), Round::Nearest)
        }),
        "FLOAT.atan2" => binary_float(values, hook, |a, b| {
            let mut value = a.clone();
            let direction = value.atan2_round(b, Round::Nearest);
            (value, direction)
        }),
        "FLOAT.min" => binary_float(values, hook, |a, b| {
            let mut value = a.clone();
            let direction = value.min_round(b, Round::Nearest);
            (value, direction)
        }),
        "FLOAT.max" => binary_float(values, hook, |a, b| {
            let mut value = a.clone();
            let direction = value.max_round(b, Round::Nearest);
            (value, direction)
        }),
        "FLOAT.lt" => compare_float(values, |ordering| ordering == Some(Ordering::Less)),
        "FLOAT.le" => compare_float(values, |ordering| {
            ordering != Some(Ordering::Greater) && ordering.is_some()
        }),
        "FLOAT.gt" => compare_float(values, |ordering| ordering == Some(Ordering::Greater)),
        "FLOAT.ge" => compare_float(values, |ordering| {
            ordering != Some(Ordering::Less) && ordering.is_some()
        }),
        "FLOAT.eq" => compare_float(values, |ordering| ordering == Some(Ordering::Equal)),
        "FLOAT.ne" => compare_float(values, |ordering| ordering != Some(Ordering::Equal)),
        "FLOAT.root" => match values {
            [Value::Float(a), b] => Some(int_value(b).and_then(|root| {
                // Every integer degree has a root (IEEE 754 rootn); MPFR takes one in a C `long`.
                let degree = root
                    .to_i64()
                    .and_then(|degree| c_long::try_from(degree).ok())
                    .ok_or_else(|| {
                        Unfolded::Unsupported(format!(
                            "FLOAT.root of degree {root} is beyond the C long MPFR's rootn takes"
                        ))
                    })?;
                a.unary_round(|value| root_of_degree(value, degree))
                    .map(Value::Float)
            })),
            _ => Some(Err(Unfolded::Unsupported(
                "constant-folding hook expected Float and Int".into(),
            ))),
        },
        "FLOAT.round" => round_float(values),
        "FLOAT.int2float" => int_to_float(values),
        "FLOAT.float2int" => unary_float(values, |a| {
            // A finite value below 2^e has an integer part of at most e bits.
            if let Some(exponent) = a.value.get_exp()
                && i64::from(exponent) > MAX_FOLDED_BITS as i64
            {
                return Err(too_large("FLOAT.float2int", exponent));
            }
            // Total, and NaN and the infinities have no nearest integer: the definition gives
            // no value there.
            let integer = a
                .value
                .to_integer_round(Round::Nearest)
                .ok_or_else(|| {
                    Unfolded::Unspecified(
                        "Float2Int of NaN or an infinity has no nearest integer.".into(),
                    )
                })?
                .0;
            Ok(BigInt::from_str(&integer.to_string())
                .map(Value::Int)
                .map_err(|error| error.to_string())?)
        }),
        "FLOAT.maxValue" => extreme_value(values, true),
        "FLOAT.minValue" => extreme_value(values, false),
        _ => None,
    }
}

/// `value` replaced by its root of degree `degree`, IEEE 754 rootn rounded to nearest at its
/// precision, and the direction of that rounding.
fn root_of_degree(value: &mut Float, degree: c_long) -> Ordering {
    let raw = value.as_raw_mut();
    // SAFETY: `raw` is the initialized `mpfr_t` of `value`, which `mpfr_rootn_si` may read and
    // write as both its operand and its result (MPFR allows the two to be the same variable).
    let ternary = unsafe { mpfr::rootn_si(raw, raw, degree, mpfr::rnd_t::RNDN) };
    ternary.cmp(&0)
}

fn unary_float(
    values: &[Value],
    operation: impl FnOnce(&KFloat) -> Result<Value, Unfolded>,
) -> Option<Result<Value, Unfolded>> {
    Some(match values {
        [Value::Float(value)] => operation(value),
        _ => Err(Unfolded::Unsupported(
            "constant-folding hook expected one Float argument".into(),
        )),
    })
}

fn float_format(values: &[Value]) -> Option<Result<Value, Unfolded>> {
    Some(match values {
        [Value::Float(value), format] => string_value(format)
            .and_then(|format| value.format(format))
            .map(Value::String),
        _ => Err(Unfolded::Unsupported(
            "constant-folding hook expected Float and String".into(),
        )),
    })
}

fn binary_float(
    values: &[Value],
    hook: &str,
    operation: impl FnOnce(&Float, &Float) -> (Float, Ordering),
) -> Option<Result<Value, Unfolded>> {
    Some(match values {
        [Value::Float(a), Value::Float(b)] => a.binary(b, hook, operation).map(Value::Float),
        _ => Err(Unfolded::Unsupported(
            "constant-folding hook expected two Float arguments".into(),
        )),
    })
}

fn compare_float(
    values: &[Value],
    predicate: impl FnOnce(Option<Ordering>) -> bool,
) -> Option<Result<Value, Unfolded>> {
    Some(match values {
        [Value::Float(a), Value::Float(b)] => {
            Ok(Value::Bool(predicate(a.value.partial_cmp(&b.value))))
        }
        _ => Err(Unfolded::Unsupported(
            "constant-folding hook expected two Float arguments".into(),
        )),
    })
}

fn round_float(values: &[Value]) -> Option<Result<Value, Unfolded>> {
    Some(match values {
        [Value::Float(value), precision, exponent] => {
            context(precision, exponent).and_then(|(precision, exponent_bits)| {
                let (value, direction) =
                    Float::with_val_round(precision, &value.value, Round::Nearest);
                KFloat::from_rounded(value, exponent_bits, direction).map(Value::Float)
            })
        }
        _ => Err(Unfolded::Unsupported(
            "constant-folding hook expected Float, Int, Int".into(),
        )),
    })
}

fn int_to_float(values: &[Value]) -> Option<Result<Value, Unfolded>> {
    Some(match values {
        [integer, precision, exponent] => int_value(integer).and_then(|integer| {
            let (precision, exponent_bits) = context(precision, exponent)?;
            let integer = Integer::from_str_radix(&integer.to_string(), 10)
                .map_err(|error| error.to_string())?;
            let (value, direction) = Float::with_val_round(precision, integer, Round::Nearest);
            KFloat::from_rounded(value, exponent_bits, direction).map(Value::Float)
        }),
        _ => Err(Unfolded::Unsupported(
            "constant-folding hook expected Int, Int, Int".into(),
        )),
    })
}

fn extreme_value(values: &[Value], maximum: bool) -> Option<Result<Value, Unfolded>> {
    Some(match values {
        [precision, exponent] => {
            context(precision, exponent).and_then(|(precision, exponent_bits)| {
                let (minimum, maximum_exponent) = exponent_limits(exponent_bits)?;
                let value = if maximum {
                    let mut value = Float::with_val(precision, 2);
                    value -= Float::with_val(precision, 2).pow(1i32 - precision as i32);
                    value *= Float::with_val(precision, 2).pow(maximum_exponent - 1);
                    value
                } else {
                    Float::with_val(precision, 2).pow(minimum - precision as i32 + 2)
                };
                Ok(Value::Float(KFloat {
                    value,
                    exponent_bits,
                }))
            })
        }
        _ => Err(Unfolded::Unsupported(
            "constant-folding hook expected two Int arguments".into(),
        )),
    })
}

fn context(precision: &Value, exponent: &Value) -> Result<(u32, u32), Unfolded> {
    let precision = int_value(precision)?.to_u32().ok_or_else(|| {
        Unfolded::Unsupported("Float precision is outside the supported range".into())
    })?;
    let exponent = int_value(exponent)?.to_u32().ok_or_else(|| {
        Unfolded::Unsupported("Float exponent bits are outside the supported range".into())
    })?;
    validate_context(precision, exponent)?;
    check_precision(precision)?;
    Ok((precision, exponent))
}

/// A precision the fold computes with: the value it describes has that many bits.
fn check_precision(precision: u32) -> Result<(), Unfolded> {
    if u64::from(precision) > MAX_FOLDED_BITS {
        return Err(too_large("FLOAT", precision));
    }
    Ok(())
}

fn validate_context(precision: u32, exponent: u32) -> Result<(u32, u32), Unfolded> {
    if precision > i32::MAX as u32 || precision > float::prec_max() {
        return Err(Unfolded::Unsupported(
            "Float precision is outside the supported range".into(),
        ));
    }
    if exponent > i32::MAX as u32 {
        return Err(Unfolded::Unsupported(
            "Float exponent bits are outside the supported range".into(),
        ));
    }
    if precision < 2 || exponent < 2 {
        return Err("Float precision and exponent bits must both be at least 2.".into());
    }
    context_exponent_limits(precision, exponent)?;
    Ok((precision, exponent))
}

fn exponent_limits(bits: u32) -> Result<(i32, i32), Unfolded> {
    let maximum = 1i32
        .checked_shl(bits.saturating_sub(1))
        .filter(|maximum| *maximum > 0)
        .ok_or_else(|| Unfolded::Unsupported("Float exponent bits are too large".into()))?;
    let minimum = 1i32
        .checked_sub(maximum)
        .ok_or_else(|| Unfolded::Unsupported("Float exponent bits are too large".into()))?;
    Ok((minimum, maximum))
}

fn context_exponent_limits(
    precision: u32,
    exponent_bits: u32,
) -> Result<(i32, i32, i32), Unfolded> {
    let (minimum, maximum) = exponent_limits(exponent_bits)?;
    let precision = i32::try_from(precision).map_err(|_| {
        Unfolded::Unsupported("Float precision is outside the supported range".into())
    })?;
    let normal_minimum = minimum.checked_add(2).ok_or_else(|| {
        Unfolded::Unsupported("Float exponent range is outside the supported range".into())
    })?;
    let subnormal_minimum = normal_minimum.checked_sub(precision - 1).ok_or_else(|| {
        Unfolded::Unsupported("Float exponent range is outside the supported range".into())
    })?;
    // K's BigFloat validates contexts against MPFR's active default range, not its wider platform limit.
    let (allowed_minimum, allowed_maximum) = (float::exp_min(), float::exp_max());
    if subnormal_minimum < allowed_minimum || maximum > allowed_maximum {
        return Err(Unfolded::Unsupported(
            "Float exponent range is outside MPFR's supported range".into(),
        ));
    }
    Ok((normal_minimum, subnormal_minimum, maximum))
}

fn limit_exponent(
    value: &mut Float,
    exponent_bits: u32,
    direction: Ordering,
) -> Result<(), Unfolded> {
    let (normal_minimum, subnormal_minimum, maximum) =
        context_exponent_limits(value.prec(), exponent_bits)?;
    let direction = value
        .clamp_exp(direction, Round::Nearest, subnormal_minimum, maximum)
        .ok_or_else(|| {
            Unfolded::Unsupported("Float exponent range is outside MPFR's supported range".into())
        })?;
    value.subnormalize_round(normal_minimum, direction, Round::Nearest);
    Ok(())
}

fn parse_parts(token: &str) -> Result<(&str, u32, u32), Unfolded> {
    if let Some((value_and_precision, exponent)) = token.rsplit_once(['x', 'X'])
        && let Some((value, precision)) = value_and_precision.rsplit_once(['p', 'P'])
    {
        return Ok((
            value,
            precision
                .parse()
                .map_err(|_| format!("invalid Float token {token:?}"))?,
            exponent
                .parse()
                .map_err(|_| format!("invalid Float token {token:?}"))?,
        ));
    }
    if let Some(value) = token.strip_suffix(['f', 'F']) {
        Ok((value, 24, 8))
    } else {
        Ok((token.strip_suffix(['d', 'D']).unwrap_or(token), 53, 11))
    }
}

fn validate_mpfr_format(format: &str) -> Result<(), Unfolded> {
    let bytes = format.as_bytes();
    let mut index = 0;
    let mut conversions = 0;
    // Invariant: `bytes[..index]` has been validated and `conversions` counts its completed conversion specifications (at most one); every iteration advances `index` or returns, so `bytes.len()` bounds the loop.
    while index < bytes.len() {
        if bytes[index] != b'%' {
            index += 1;
            continue;
        }
        index += 1;
        if bytes.get(index) == Some(&b'%') {
            index += 1;
            continue;
        }
        let mut is_mpfr = false;
        let mut completed = false;
        // Invariant: `bytes[index]` is the next byte of the current `%` specification, `is_mpfr` records whether it has shown an `R` modifier, and `completed` is false; each iteration advances `index` by one or leaves the loop.
        while let Some(&byte) = bytes.get(index) {
            if byte == b'*' || byte == b'$' {
                return Err("MPFR Float formats cannot use dynamic or positional arguments".into());
            }
            if byte == b'R' {
                is_mpfr = true;
            }
            if byte.is_ascii_alphabetic()
                && byte != b'R'
                && !matches!(byte, b'N' | b'Z' | b'U' | b'D' | b'Y' | b'A')
            {
                if !is_mpfr
                    || !matches!(
                        byte,
                        b'a' | b'A' | b'b' | b'e' | b'E' | b'f' | b'F' | b'g' | b'G'
                    )
                {
                    return Err("Float format must use an MPFR floating-point conversion".into());
                }
                conversions += 1;
                if conversions > 1 {
                    return Err("Float format can contain at most one conversion".into());
                }
                index += 1;
                completed = true;
                break;
            }
            index += 1;
        }
        if !completed {
            return Err("incomplete MPFR Float format".into());
        }
    }
    Ok(())
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use super::*;

    fn float(token: &str) -> KFloat {
        KFloat::parse(token).unwrap()
    }

    fn folded_float(hook: &str, values: Vec<Value>) -> KFloat {
        match evaluate(hook, &values).unwrap().unwrap() {
            Value::Float(value) => value,
            value => panic!("expected Float, got {value:?}"),
        }
    }

    fn folded_int(hook: &str, values: Vec<Value>) -> BigInt {
        match evaluate(hook, &values).unwrap().unwrap() {
            Value::Int(value) => value,
            value => panic!("expected Int, got {value:?}"),
        }
    }

    #[test]
    fn spells_float_tokens_with_precision_and_exponent_width_suffixes() {
        assert_eq!(float("0.1").token(), "1.0000000000000001e-01p53x11");
        assert_eq!(float("0.1f").token(), "1.00000001e-01p24x8");
        assert_eq!(float("0").token(), "0e+00p53x11");
        assert_eq!(float("-0").token(), "-0e+00p53x11");
        assert_eq!(float("Infinity").token(), "Infinityp53x11");
        assert_eq!(float("-Infinity").token(), "-Infinityp53x11");
        assert_eq!(float("NaN").token(), "NaNp53x11");
    }

    #[test]
    fn rounds_halfway_values_to_even() {
        let two = Value::Int(2.into());
        let eight = Value::Int(8.into());
        let high = folded_float(
            "FLOAT.round",
            vec![Value::Float(float("10.5")), two.clone(), eight.clone()],
        );
        let low = folded_float("FLOAT.round", vec![Value::Float(float("9.5")), two, eight]);
        assert_eq!(high.value.to_f64(), 12.0);
        assert_eq!(low.value.to_f64(), 8.0);
    }

    #[test]
    fn folds_float_edge_values_keeping_precision_and_exponent() {
        // binary64 (p53x11): negating +0 gives -0; floor and ceil of -10.5 round toward -inf and
        // +inf; `rem` is the IEEE remainder, 7 - 2 x 4 = -1 (the quotient 3.5 rounds to even);
        // 0/0 is NaN and 1/0 is +inf. Each result keeps its operands' precision and exponent width.
        for (hook, operands, expected) in [
            ("FLOAT.neg", &["0.0"][..], "-0e+00p53x11"),
            (
                "FLOAT.floor",
                &["-10.5"][..],
                "-1.1000000000000000e+01p53x11",
            ),
            (
                "FLOAT.ceil",
                &["-10.5"][..],
                "-1.0000000000000000e+01p53x11",
            ),
            (
                "FLOAT.rem",
                &["7.0", "2.0"][..],
                "-1.0000000000000000e+00p53x11",
            ),
            ("FLOAT.div", &["0.0", "0.0"][..], "NaNp53x11"),
            ("FLOAT.div", &["1.0", "0.0"][..], "Infinityp53x11"),
        ] {
            let values = operands
                .iter()
                .map(|operand| Value::Float(float(operand)))
                .collect();
            assert_eq!(folded_float(hook, values).token(), expected, "{hook}");
        }
    }

    /// `truncFloat` rounds toward zero, exactly and keeping the sign of a zero result.
    #[test]
    fn truncates_toward_zero() {
        for (operand, expected) in [
            ("-2.5", "-2.0000000000000000e+00p53x11"),
            ("2.5f", "2.00000000e+00p24x8"),
            ("-0.5", "-0e+00p53x11"),
            ("Infinity", "Infinityp53x11"),
            ("NaN", "NaNp53x11"),
        ] {
            assert_eq!(
                folded_float("FLOAT.trunc", vec![Value::Float(float(operand))]).token(),
                expected,
                "{operand}"
            );
        }
    }

    /// `String2Float` reads the syntax of the `Float` sort; MPFR's parser also accepts spaces,
    /// `inf`, `nan`, `@`-exponents and signed `.5`, which are not Float tokens.
    #[test]
    fn reads_only_float_syntax() {
        for token in [
            "1",
            "+1",
            "-1.",
            ".5",
            "1.5e-3",
            "1E+5",
            "2d",
            "1.5F",
            "1p24x8",
            "1P53X11",
            "Infinity",
            "+Infinity",
            "-Infinityf",
            "NaN",
            "NaNp24x8",
        ] {
            assert!(KFloat::parse(token).is_ok(), "{token:?}");
        }
        for token in [
            "",
            " 1",
            "1 ",
            "inf",
            "nan",
            "-NaN",
            "Inf",
            "@inf@",
            "1@2",
            "-.5",
            "+.5",
            "1e",
            "1_0",
            "0x10",
            "1p24",
            "1p+24x8",
            "1.5.5",
            "e5",
            ".",
            "Infinityx",
        ] {
            assert!(KFloat::parse(token).is_err(), "{token:?}");
            assert!(
                evaluate("STRING.string2float", &[Value::String(token.into())])
                    .unwrap()
                    .is_err(),
                "{token:?}"
            );
        }
    }

    #[test]
    fn respects_ieee_exponent_ranges_and_subnormals() {
        let precision = Value::Int(24.into());
        let exponent = Value::Int(8.into());
        let minimum = folded_float("FLOAT.minValue", vec![precision.clone(), exponent.clone()]);
        let maximum = folded_float("FLOAT.maxValue", vec![precision, exponent]);
        assert_eq!(minimum.value.to_f32(), f32::MIN_POSITIVE * f32::EPSILON);
        assert_eq!(maximum.value.to_f32(), f32::MAX);
        assert_eq!(
            folded_int("FLOAT.exponent", vec![Value::Float(minimum)]),
            BigInt::from(-127)
        );
        assert!(float("3.4028236e38p24x8").value.is_infinite());
        assert!(float("1e-50p24x8").value.is_zero());
    }

    #[test]
    fn delegates_explicit_formats_to_mpfr_safely() {
        assert_eq!(float("12.5").format("%.2RNf").unwrap(), "12.50");
        assert_eq!(
            float("12.5").format("value=%+.1RNe").unwrap(),
            "value=+1.2e+01"
        );
        assert!(float("12.5").format("%s").is_err());
        assert!(float("12.5").format("%Rf %Rf").is_err());
    }

    #[test]
    fn enforces_explicit_float_context_boundaries() {
        for token in [
            "1p0x8",
            "NaNp1x8",
            "1p24x0",
            "Infinityp24x1",
            "1p2147483648x8",
            "NaNp24x2147483648",
            "1p24x31",
            "NaNp24x31",
            "1p24x32",
        ] {
            assert_eq!(
                KFloat::parse(token).unwrap_err().message(),
                format!("invalid Float token {token:?}")
            );
        }

        let finite = KFloat::parse("1p24x30").unwrap();
        assert_eq!(finite.value.prec(), 24);
        assert_eq!(finite.exponent_bits, 30);
        let special = KFloat::parse("NaNp24x30").unwrap();
        assert!(special.value.is_nan());
        assert_eq!(special.value.prec(), 24);
        assert_eq!(special.exponent_bits, 30);
    }

    /// `rootFloat(F, N)` is the Nth root: the even root of -0 is +0 and the odd root -0, so
    /// `sqrtFloat(-0.0)`, which `domains.md` defines as `rootFloat(F, 2)`, is +0.
    #[test]
    fn roots_negative_zero_by_the_parity_of_the_degree() {
        let root = |degree: i64| match evaluate(
            "FLOAT.root",
            &[Value::Float(float("-0.0")), Value::Int(degree.into())],
        ) {
            Some(Ok(Value::Float(value))) => value.token(),
            other => panic!("rootFloat(-0.0, {degree}) gave {other:?}"),
        };
        assert_eq!(root(2), "0e+00p53x11");
        assert_eq!(root(4), "0e+00p53x11");
        assert_eq!(root(3), "-0e+00p53x11");
    }

    /// The two evaluators compute `rootFloat` independently (MPFR here, an exact rounding search
    /// in the backend); both must give the correctly rounded IEEE rootn, so they agree on every
    /// value and degree: binary64 and binary32 values spread over the whole exponent range
    /// (bit patterns from a fixed linear congruential sequence) and every degree from -12 to 12
    /// and a few far beyond 32 bits.
    #[test]
    fn roots_agree_with_the_backend_on_every_degree() {
        use crate::names::BuiltinSort;
        let backend_root = |token: &str, degree: &BigInt| {
            let result = k_rust_backend::builtin::evaluate_hook(
                "FLOAT.root",
                &[
                    k_rust_backend::term::Term::raw_domain_value(
                        k_rust_backend::term::Sort::builtin(BuiltinSort::Float),
                        token,
                    ),
                    k_rust_backend::term::Term::raw_domain_value(
                        k_rust_backend::term::Sort::builtin(BuiltinSort::Int),
                        degree.to_string(),
                    ),
                ],
            );
            let Ok(Ok(k_rust_backend::builtin::BuiltinResult::Value(value))) = result else {
                panic!("the backend gives {result:?} for rootFloat({token}, {degree})");
            };
            let k_rust_backend::term::TermKind::DomainValue { value, .. } = value.kind() else {
                panic!("a Float domain value");
            };
            float(value.as_utf8().unwrap())
        };
        let mut state = 0x2545_f491_4f6c_dd1d_u64;
        let mut next = || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            state
        };
        let mut tokens = vec!["1.0".to_owned(), "0.5f".to_owned()];
        for _ in 0..60 {
            let double = f64::from_bits(next() & 0x7fff_ffff_ffff_ffff);
            let single = f32::from_bits((next() >> 33) as u32);
            for value in [double, -double] {
                if value.is_finite() {
                    tokens.push(format!("{value:e}"));
                }
            }
            if single.is_finite() {
                tokens.push(format!("{single:e}f"));
            }
        }
        let degrees = (-12..=12)
            .map(BigInt::from)
            .chain([
                BigInt::from(1u64 << 33) + 1,
                -BigInt::from(1u64 << 35),
                BigInt::from(i64::MAX),
            ])
            .collect::<Vec<_>>();
        for token in &tokens {
            for degree in &degrees {
                let Some(Ok(Value::Float(folded))) = evaluate(
                    "FLOAT.root",
                    &[Value::Float(float(token)), Value::Int(degree.clone())],
                ) else {
                    panic!("rootFloat({token}, {degree}) is not folded");
                };
                assert_eq!(
                    folded.token(),
                    backend_root(token, degree).token(),
                    "rootFloat({token}, {degree})"
                );
            }
        }
    }

    /// Every integer degree has a root, so a degree outside 32 bits is folded like any other
    /// (MPFR takes a C `long`), to the backend's value; a degree beyond that is left for
    /// execution as one the fold does not compute, not as an undefined application.
    #[test]
    fn folds_roots_of_degrees_beyond_32_bits() {
        use crate::names::BuiltinSort;
        let two_31 = BigInt::from(1u64 << 31);
        for degree in [
            two_31.clone(),
            -two_31.clone() - 1,
            BigInt::from(1u64 << 40),
        ] {
            for token in ["2.0", "1.0e-300", "123.456f"] {
                let folded = match evaluate(
                    "FLOAT.root",
                    &[Value::Float(float(token)), Value::Int(degree.clone())],
                ) {
                    Some(Ok(Value::Float(value))) => value.token(),
                    other => panic!("rootFloat({token}, {degree}) gave {other:?}"),
                };
                let backend = k_rust_backend::builtin::evaluate_hook(
                    "FLOAT.root",
                    &[
                        k_rust_backend::term::Term::raw_domain_value(
                            k_rust_backend::term::Sort::builtin(BuiltinSort::Float),
                            token,
                        ),
                        k_rust_backend::term::Term::raw_domain_value(
                            k_rust_backend::term::Sort::builtin(BuiltinSort::Int),
                            degree.to_string(),
                        ),
                    ],
                );
                let Ok(Ok(k_rust_backend::builtin::BuiltinResult::Value(value))) = backend else {
                    panic!("the backend gives {backend:?} for rootFloat({token}, {degree})");
                };
                let k_rust_backend::term::TermKind::DomainValue { value, .. } = value.kind() else {
                    panic!("a Float domain value");
                };
                assert_eq!(
                    folded,
                    value.as_utf8().unwrap(),
                    "rootFloat({token}, {degree})"
                );
            }
        }
        assert!(matches!(
            evaluate(
                "FLOAT.root",
                &[
                    Value::Float(float("2.0")),
                    Value::Int(BigInt::from(1) << 64)
                ],
            ),
            Some(Err(Unfolded::Unsupported(_)))
        ));
    }

    /// `Float2Int` is total, and NaN and the infinities have no nearest integer, so its value
    /// there is not given and the application stays.
    #[test]
    fn leaves_float2int_of_nan_and_infinities_unfolded() {
        for token in ["NaN", "Infinity", "-Infinityf"] {
            assert!(
                matches!(
                    evaluate("FLOAT.float2int", &[Value::Float(float(token))]),
                    Some(Err(Unfolded::Unspecified(_)))
                ),
                "Float2Int({token})"
            );
        }
        assert_eq!(
            folded_int("FLOAT.float2int", vec![Value::Float(float("-2.5"))]),
            BigInt::from(-2)
        );
    }

    /// The fold's output is the definition every route loads, proofs included, so it does not
    /// choose a result format for an operation over a binary32 and a binary64 operand: every binary
    /// Float-valued hook leaves such a pair unfolded, as a value the definition leaves open. A
    /// comparison needs no result format and is folded.
    #[test]
    fn leaves_operations_over_two_formats_unfolded_as_unspecified() {
        for hook in [
            "FLOAT.add",
            "FLOAT.sub",
            "FLOAT.mul",
            "FLOAT.div",
            "FLOAT.rem",
            "FLOAT.pow",
            "FLOAT.atan2",
            "FLOAT.min",
            "FLOAT.max",
        ] {
            for (left, right) in [("0.1f", "2.0"), ("2.0", "0.1f")] {
                let values = [Value::Float(float(left)), Value::Float(float(right))];
                assert!(
                    matches!(evaluate(hook, &values), Some(Err(Unfolded::Unspecified(_)))),
                    "{hook}({left}, {right}): {:?}",
                    evaluate(hook, &values)
                );
            }
        }
        assert!(matches!(
            evaluate(
                "FLOAT.gt",
                &[Value::Float(float("0.1f")), Value::Float(float("0.1"))]
            ),
            Some(Ok(Value::Bool(true)))
        ));
    }

    /// A Float of more than 2^20 bits of precision is left unfolded, whether a hook would build
    /// it or a token names it.
    #[test]
    fn leaves_floats_above_the_result_bound_unfolded() {
        let int = |value: i64| Value::Int(value.into());
        let converted = |precision: i64| {
            int_to_float(&[int(1), int(precision), int(11)]).expect("Int2Float has an evaluator")
        };
        assert!(converted(1 << 20).is_ok());
        assert!(matches!(
            converted((1 << 20) + 1),
            Err(Unfolded::TooLarge(_))
        ));
        assert!(KFloat::parse("1.5p1048576x11").is_ok());
        assert!(matches!(
            KFloat::parse("1.5p1048577x11"),
            Err(Unfolded::TooLarge(_))
        ));
        let huge = KFloat::parse("1e400000p53x30").unwrap();
        assert!(matches!(
            evaluate("FLOAT.float2int", &[Value::Float(huge)]),
            Some(Err(Unfolded::TooLarge(_)))
        ));
    }

    #[test]
    fn rejects_invalid_operation_contexts() {
        let context_error = |precision: i64, exponent: i64| {
            context(&Value::Int(precision.into()), &Value::Int(exponent.into()))
                .unwrap_err()
                .message()
                .to_owned()
        };

        assert_eq!(
            context_error(1, 8),
            "Float precision and exponent bits must both be at least 2."
        );
        assert_eq!(
            context_error(24, 1),
            "Float precision and exponent bits must both be at least 2."
        );
        assert_eq!(
            context_error(i64::from(i32::MAX) + 1, 8),
            "Float precision is outside the supported range"
        );
        assert_eq!(
            context_error(24, i64::from(i32::MAX) + 1),
            "Float exponent bits are outside the supported range"
        );
        assert_eq!(
            context(&Value::Int(24.into()), &Value::Int(30.into())),
            Ok((24, 30))
        );
        assert_eq!(
            context_error(24, 31),
            "Float exponent range is outside MPFR's supported range"
        );
        assert_eq!(context_error(24, 32), "Float exponent bits are too large");
    }

    /// The exact decimal literal of `±mantissa * 2^exponent` in the format `pNxM`.
    fn exact_literal(
        negative: bool,
        mantissa: &BigInt,
        exponent: i64,
        format: (u32, u32),
    ) -> String {
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
    /// (ties to infinity), half the least subnormal (ties to zero), the largest subnormal plus
    /// half an ulp (the least normal), an all-ones significand plus half an ulp (carries into the
    /// next binade), exact midpoints between neighbours, each moved by `±10^-k`, and negated.
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
        let mut state =
            0x2545_f491_4f6c_dd1d_u64 ^ (u64::from(format.0) << 32) ^ u64::from(format.1);
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

    /// `(negative, num, den)` of a finite canonical text `[-]DeQpNxM`.
    fn decoded(text: &str) -> Option<(bool, BigInt, BigInt)> {
        let body = &text[..text.rfind('p').unwrap()];
        let (negative, body) = match body.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, body),
        };
        let (digits, exponent) = body.split_once(['e', 'E'])?;
        let digits: BigInt = digits.replace('.', "").parse().ok()?;
        let fraction = body.split_once('.').map_or(0, |(_, rest)| {
            rest.split_once(['e', 'E'])
                .map_or(rest.len(), |(fraction, _)| fraction.len())
        });
        let exponent = exponent.parse::<i64>().ok()? - fraction as i64;
        let power = BigInt::from(10).pow(exponent.unsigned_abs() as u32);
        Some(if exponent < 0 {
            (negative, digits, power)
        } else {
            (negative, digits * power, BigInt::from(1))
        })
    }

    /// The backend's canonical text of a Float literal, built at load and by `String2Float`
    /// for every format, agrees with MPFR: it is the canonical text of the token the fold
    /// writes for the literal (`KFloat::parse`, whose exponent range follows IEEE through the
    /// fold's own conversion), and it denotes exactly the MPFR value. Literals the backend
    /// refuses for its size bound are excluded, and the refusal agrees with its estimate.
    #[test]
    fn the_backend_canonical_float_text_agrees_with_mpfr() {
        use k_rust_backend::builtin::{
            FloatTextRefusal, MAX_FLOAT_CANONICAL_BITS, canonical_float_text,
            float_canonical_bits_estimate,
        };
        let mut checked = 0;
        for (format, random) in [
            ((2, 2), 200),
            ((3, 3), 200),
            ((5, 4), 200),
            ((11, 5), 600),
            ((24, 8), 600),
            ((53, 11), 600),
            ((64, 15), 300),
            ((113, 15), 300),
            ((237, 17), 60),
        ] {
            let mut literals = boundary_literals(format);
            literals.extend(random_literals(format, random));
            for literal in literals {
                let text = match canonical_float_text(&literal) {
                    Ok(text) => text,
                    Err(refusal @ FloatTextRefusal::BeyondBound { estimate_bits }) => {
                        assert!(estimate_bits > MAX_FLOAT_CANONICAL_BITS, "{literal}");
                        assert_eq!(float_canonical_bits_estimate(&literal), Err(refusal));
                        continue;
                    }
                    Err(refusal) => panic!("{literal}: {refusal:?}"),
                };
                let mpfr = KFloat::parse(&literal).unwrap();
                assert_eq!(
                    canonical_float_text(&mpfr.token()).as_ref(),
                    Ok(&text),
                    "{literal}: MPFR wrote {}",
                    mpfr.token()
                );
                let value = &mpfr.value;
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
                } else {
                    // binary32 and binary64 texts are the hooks' round-trip decimals, read by
                    // the hooks' correctly rounded parse; other formats are exact decimals.
                    let (negative, num, den) = if matches!(format, (24, 8) | (53, 11)) {
                        let body = &text[..text.rfind('p').unwrap()];
                        let native = if format.0 == 24 {
                            f64::from(body.parse::<f32>().unwrap())
                        } else {
                            body.parse::<f64>().unwrap()
                        };
                        let (mantissa, exponent) = Float::with_val(64, native.abs())
                            .to_integer_exp()
                            .map(|(mantissa, exponent)| {
                                (BigInt::from_str(&mantissa.to_string()).unwrap(), exponent)
                            })
                            .unwrap_or((BigInt::from(0), 0));
                        let power = BigInt::from(1) << u64::from(exponent.unsigned_abs());
                        if exponent < 0 {
                            (native.is_sign_negative(), mantissa, power)
                        } else {
                            (native.is_sign_negative(), mantissa * power, BigInt::from(1))
                        }
                    } else {
                        decoded(&text).unwrap()
                    };
                    assert_eq!(negative, value.is_sign_negative(), "{literal}: {text}");
                    let (mantissa, exponent) = value
                        .to_integer_exp()
                        .map(|(mantissa, exponent)| {
                            (BigInt::from_str(&mantissa.to_string()).unwrap(), exponent)
                        })
                        .unwrap_or((BigInt::from(0), 0));
                    let mantissa = if negative { -mantissa } else { mantissa };
                    // num/den = mantissa * 2^exponent
                    let (left, right) = if exponent < 0 {
                        (num << exponent.unsigned_abs() as u64, mantissa * den)
                    } else {
                        (num, (mantissa << exponent as u64) * den)
                    };
                    assert_eq!(left, right, "{literal}: {text} against MPFR");
                }
                checked += 1;
            }
        }
        assert!(checked > 3000, "only {checked} literals were checked");
    }

    /// A folded Float result is written only where the backend loads it: one whose canonical
    /// text, the exact decimal of a 400000-bit quotient, is beyond `MAX_FLOAT_CANONICAL_BITS` is
    /// left for execution; a short one is written.
    #[test]
    fn leaves_unfolded_a_float_result_whose_canonical_text_is_beyond_the_backend_bound() {
        let quotient = |precision: u32| {
            folded_float(
                "FLOAT.div",
                vec![
                    Value::Float(float(&format!("1.0p{precision}x11"))),
                    Value::Float(float(&format!("3.0p{precision}x11"))),
                ],
            )
            .token()
        };
        assert!(super::super::loadable_float("FLOAT.div", &quotient(113)).is_ok());
        assert!(matches!(
            super::super::loadable_float("FLOAT.div", &quotient(400_000)),
            Err(Unfolded::TooLarge(_))
        ));
    }

    /// A finite value whose token would exceed `MAX_FOLDED_BITS` has no token the fold writes:
    /// `try_token` and `Float2String` are `TooLarge`, decided from the precision, and a value of
    /// 400,000 bits still has one.
    #[test]
    fn a_token_beyond_the_written_bound_is_too_large() {
        let wide = float("1.0p500000x20");
        assert!(matches!(wide.try_token(), Err(Unfolded::TooLarge(_))));
        assert!(matches!(
            evaluate("STRING.float2string", &[Value::Float(wide)]),
            Some(Err(Unfolded::TooLarge(_)))
        ));
        assert!(float("1.0p400000x20").try_token().is_ok());
        assert!(float("Infinityp500000x20").try_token().is_ok());
    }
}
