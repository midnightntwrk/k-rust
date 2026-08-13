//! MPFR-backed implementation of K's `FLOAT` constant-folding hooks.

use std::{
    cmp::Ordering,
    ffi::{CStr, CString},
    ptr,
    str::FromStr,
};

use gmp_mpfr_sys::mpfr;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use rug::{
    Float, Integer,
    float::{Round, Special},
    ops::Pow,
};

use super::{Value, int_value, string_value};

#[derive(Clone, Debug)]
pub(super) struct KFloat {
    value: Float,
    exponent_bits: u32,
}

impl KFloat {
    pub(super) fn parse(token: &str) -> Result<Self, String> {
        let (text, precision, exponent_bits) = parse_parts(token)?;
        match text {
            "Infinity" => Ok(Self::special(precision, exponent_bits, Special::Infinity)),
            "-Infinity" => Ok(Self::special(
                precision,
                exponent_bits,
                Special::NegInfinity,
            )),
            "NaN" => Ok(Self::special(precision, exponent_bits, Special::Nan)),
            text => {
                let parsed =
                    Float::parse(text).map_err(|_| format!("invalid Float token {token:?}"))?;
                let (value, direction) = Float::with_val_round(precision, parsed, Round::Nearest);
                Self::from_rounded(value, exponent_bits, direction)
            }
        }
    }

    pub(super) fn token(&self) -> String {
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
            self.format("%Re")
                .expect("the fixed MPFR token format must be valid")
        };
        format!("{value}p{}x{}", self.value.prec(), self.exponent_bits)
    }

    fn format(&self, format: &str) -> Result<String, String> {
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
            CStr::from_bytes_with_nul(&buffer)
                .map_err(|error| error.to_string())?
                .to_str()
                .map(str::to_owned)
                .map_err(|error| error.to_string())
        }
    }

    fn context_matches(&self, other: &Self, hook: &str) -> Result<(), String> {
        if self.value.prec() == other.value.prec() && self.exponent_bits == other.exponent_bits {
            Ok(())
        } else {
            Err(format!(
                "Arguments to hook {hook} do not match in exponent bits and precision."
            ))
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
    ) -> Result<Self, String> {
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

    fn unary_round(&self, operation: impl FnOnce(&mut Float) -> Ordering) -> Result<Self, String> {
        let mut value = self.value.clone();
        let direction = operation(&mut value);
        Self::from_rounded(value, self.exponent_bits, direction)
    }

    fn binary(
        &self,
        other: &Self,
        hook: &str,
        operation: impl FnOnce(&Float, &Float) -> (Float, Ordering),
    ) -> Result<Self, String> {
        self.context_matches(other, hook)?;
        let (value, direction) = operation(&self.value, &other.value);
        Self::from_rounded(value, self.exponent_bits, direction)
    }
}

pub(super) fn evaluate(hook: &str, values: &[Value]) -> Option<Result<Value, String>> {
    match hook {
        "STRING.float2string" => unary_float(values, |a| Ok(Value::String(a.token()))),
        "STRING.floatFormat" => float_format(values),
        "STRING.string2float" => match values {
            [value] => Some(string_value(value).and_then(KFloat::parse).map(Value::Float)),
            _ => Some(Err("constant-folding hook expected one argument".into())),
        },
        "FLOAT.precision" => unary_float(values, |a| Ok(Value::Int(a.value.prec().into()))),
        "FLOAT.exponentBits" => {
            unary_float(values, |a| Ok(Value::Int(a.exponent_bits.into())))
        }
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
        "FLOAT.le" => compare_float(values, |ordering| ordering != Some(Ordering::Greater) && ordering.is_some()),
        "FLOAT.gt" => compare_float(values, |ordering| ordering == Some(Ordering::Greater)),
        "FLOAT.ge" => compare_float(values, |ordering| ordering != Some(Ordering::Less) && ordering.is_some()),
        "FLOAT.eq" => compare_float(values, |ordering| ordering == Some(Ordering::Equal)),
        "FLOAT.ne" => compare_float(values, |ordering| ordering != Some(Ordering::Equal)),
        "FLOAT.root" => match values {
            [Value::Float(a), b] => Some(int_value(b).and_then(|root| {
                let root = root.to_i32().ok_or_else(|| "Argument to hook FLOAT.root out of range. Expected a 32-bit signed integer.".to_owned())?;
                a.unary_round(|value| value.root_i_round(root, Round::Nearest))
                    .map(Value::Float)
            })),
            _ => Some(Err("constant-folding hook expected Float and Int".into())),
        },
        "FLOAT.round" => round_float(values),
        "FLOAT.int2float" => int_to_float(values),
        "FLOAT.float2int" => unary_float(values, |a| {
            let integer = a.value.to_integer_round(Round::Nearest).ok_or_else(|| "Argument to hook FLOAT.float2int cannot be rounded to an integer.".to_owned())?.0;
            BigInt::from_str(&integer.to_string()).map(Value::Int).map_err(|error| error.to_string())
        }),
        "FLOAT.maxValue" => extreme_value(values, true),
        "FLOAT.minValue" => extreme_value(values, false),
        _ => None,
    }
}

fn unary_float(
    values: &[Value],
    operation: impl FnOnce(&KFloat) -> Result<Value, String>,
) -> Option<Result<Value, String>> {
    Some(match values {
        [Value::Float(value)] => operation(value),
        _ => Err("constant-folding hook expected one Float argument".into()),
    })
}

fn float_format(values: &[Value]) -> Option<Result<Value, String>> {
    Some(match values {
        [Value::Float(value), format] => string_value(format)
            .and_then(|format| value.format(format))
            .map(Value::String),
        _ => Err("constant-folding hook expected Float and String".into()),
    })
}

fn binary_float(
    values: &[Value],
    hook: &str,
    operation: impl FnOnce(&Float, &Float) -> (Float, Ordering),
) -> Option<Result<Value, String>> {
    Some(match values {
        [Value::Float(a), Value::Float(b)] => a.binary(b, hook, operation).map(Value::Float),
        _ => Err("constant-folding hook expected two Float arguments".into()),
    })
}

fn compare_float(
    values: &[Value],
    predicate: impl FnOnce(Option<Ordering>) -> bool,
) -> Option<Result<Value, String>> {
    Some(match values {
        [Value::Float(a), Value::Float(b)] => {
            Ok(Value::Bool(predicate(a.value.partial_cmp(&b.value))))
        }
        _ => Err("constant-folding hook expected two Float arguments".into()),
    })
}

fn round_float(values: &[Value]) -> Option<Result<Value, String>> {
    Some(match values {
        [Value::Float(value), precision, exponent] => {
            context(precision, exponent).and_then(|(precision, exponent_bits)| {
                let (value, direction) =
                    Float::with_val_round(precision, &value.value, Round::Nearest);
                KFloat::from_rounded(value, exponent_bits, direction).map(Value::Float)
            })
        }
        _ => Err("constant-folding hook expected Float, Int, Int".into()),
    })
}

fn int_to_float(values: &[Value]) -> Option<Result<Value, String>> {
    Some(match values {
        [integer, precision, exponent] => int_value(integer).and_then(|integer| {
            let (precision, exponent_bits) = context(precision, exponent)?;
            let integer = Integer::from_str_radix(&integer.to_string(), 10)
                .map_err(|error| error.to_string())?;
            let (value, direction) = Float::with_val_round(precision, integer, Round::Nearest);
            KFloat::from_rounded(value, exponent_bits, direction).map(Value::Float)
        }),
        _ => Err("constant-folding hook expected Int, Int, Int".into()),
    })
}

fn extreme_value(values: &[Value], maximum: bool) -> Option<Result<Value, String>> {
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
        _ => Err("constant-folding hook expected two Int arguments".into()),
    })
}

fn context(precision: &Value, exponent: &Value) -> Result<(u32, u32), String> {
    let precision = int_value(precision)?
        .to_u32()
        .ok_or_else(|| "Float precision is outside the supported range".to_owned())?;
    let exponent = int_value(exponent)?
        .to_u32()
        .ok_or_else(|| "Float exponent bits are outside the supported range".to_owned())?;
    if precision < 2 || exponent < 2 {
        return Err("Float precision and exponent bits must both be at least 2.".into());
    }
    Ok((precision, exponent))
}

fn exponent_limits(bits: u32) -> Result<(i32, i32), String> {
    let maximum = 1i32
        .checked_shl(bits.saturating_sub(1))
        .ok_or_else(|| "Float exponent bits are too large".to_owned())?;
    Ok((1 - maximum, maximum))
}

fn limit_exponent(
    value: &mut Float,
    exponent_bits: u32,
    direction: Ordering,
) -> Result<(), String> {
    let (minimum, maximum) = exponent_limits(exponent_bits)?;
    let precision = i32::try_from(value.prec())
        .map_err(|_| "Float precision is outside the supported range".to_owned())?;
    let normal_minimum = minimum
        .checked_add(2)
        .ok_or_else(|| "Float exponent range is outside the supported range".to_owned())?;
    let subnormal_minimum = normal_minimum
        .checked_sub(precision - 1)
        .ok_or_else(|| "Float exponent range is outside the supported range".to_owned())?;
    let direction = value
        .clamp_exp(direction, Round::Nearest, subnormal_minimum, maximum)
        .ok_or_else(|| "Float exponent range is outside MPFR's supported range".to_owned())?;
    value.subnormalize_round(normal_minimum, direction, Round::Nearest);
    Ok(())
}

fn parse_parts(token: &str) -> Result<(&str, u32, u32), String> {
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

fn validate_mpfr_format(format: &str) -> Result<(), String> {
    let bytes = format.as_bytes();
    let mut index = 0;
    let mut conversions = 0;
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
    fn spells_k_float_tokens_like_mpfr_java() {
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
}
