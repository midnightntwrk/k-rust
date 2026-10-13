//! Portable IEEE binary32/binary64 implementations of K's `FLOAT` hooks.

use num_bigint::BigInt;
use num_traits::{FromPrimitive, ToPrimitive};

use k_rust_kore::names::BuiltinSort;

use super::{
    BuiltinError, BuiltinResult, HookResult, UnsupportedHookReason, bool_term, expect_arity,
    int_term, read_int,
};
use crate::term::{DomainKind, Sort, Term, TermKind};

mod root;

#[derive(Clone, Copy, Debug)]
enum KFloat {
    Binary32(f32),
    Binary64(f64),
}

#[derive(Clone, Copy)]
enum BinaryOperation {
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
}

impl BinaryOperation {
    /// The Float-valued binary operation `hook` names, for the six the backend evaluates.
    fn of(hook: &str) -> Option<Self> {
        Some(match hook {
            "FLOAT.add" => Self::Add,
            "FLOAT.sub" => Self::Sub,
            "FLOAT.mul" => Self::Mul,
            "FLOAT.div" => Self::Div,
            "FLOAT.min" => Self::Min,
            "FLOAT.max" => Self::Max,
            _ => return None,
        })
    }

    fn binary32(self, left: f32, right: f32) -> f32 {
        match self {
            Self::Add => left + right,
            Self::Sub => left - right,
            Self::Mul => left * right,
            Self::Div => left / right,
            Self::Min => minimum_f32(left, right),
            Self::Max => maximum_f32(left, right),
        }
    }

    fn binary64(self, left: f64, right: f64) -> f64 {
        match self {
            Self::Add => left + right,
            Self::Sub => left - right,
            Self::Mul => left * right,
            Self::Div => left / right,
            Self::Min => minimum_f64(left, right),
            Self::Max => maximum_f64(left, right),
        }
    }
}

/// The operands of a binary Float operation of which one is binary32 and the other binary64, in
/// their argument order.
///
/// `domains.md` names no format for such an operation's result. IEEE 754 defines an operation as
/// its exact result rounded once to a destination format and leaves the destination of operands
/// of two formats to the language; k-rust's reading, applied only in an execution, takes the
/// operand format that contains the other, binary64 (the destination IEEE 754-2008 10.3 gives
/// under `preferredWidthNone`): every binary32 value, subnormals, infinities, signed zeros and
/// NaN included, is a binary64 value, so the binary32 operand widens exactly and the result is
/// rounded once.
#[derive(Clone, Copy, Debug)]
pub(crate) struct MixedPair {
    left: KFloat,
    right: KFloat,
}

impl MixedPair {
    /// The pair `left`, `right` when their formats are binary32 and binary64, in either order.
    fn of(left: KFloat, right: KFloat) -> Option<Self> {
        matches!(
            (left, right),
            (KFloat::Binary32(_), KFloat::Binary64(_)) | (KFloat::Binary64(_), KFloat::Binary32(_))
        )
        .then_some(Self { left, right })
    }

    /// Both operands in the destination format, binary64; exact.
    fn widened(self) -> (f64, f64) {
        (self.left.as_f64(), self.right.as_f64())
    }

    /// Why the definition leaves `hook`'s value on this pair to a reading, for the
    /// unevaluated application outside an execution.
    pub(crate) fn detail(self, hook: &str) -> String {
        format!(
            "{hook} of a Float of precision {} with {} exponent bits and one of precision {} with \
             {} exponent bits rounds to a result format domains.md does not name; k-rust's \
             reading, binary64, applies only in an execution",
            self.left.precision(),
            self.left.exponent_bits(),
            self.right.precision(),
            self.right.exponent_bits(),
        )
    }
}

/// The binary32 and binary64 operands of `hook` applied to `arguments`, when `hook` is one of the
/// Float-valued binary hooks the backend evaluates (`+Float`, `-Float`, `*Float`, `/Float`,
/// `minFloat`, `maxFloat`) and the evaluator reads its two arguments as one binary32 and one
/// binary64 value; `None` otherwise.
///
/// The arguments are read exactly as the evaluator reads them (`read_operands`), and the pair is
/// the one the evaluator widens (`KFloat::binary`), so every application on which the evaluator
/// takes the binary64 reading is named here, whatever spelling its operands use. Comparisons are
/// not named: they need no destination format.
pub(crate) fn mixed_destination(hook: &str, arguments: &[Term]) -> Option<MixedPair> {
    BinaryOperation::of(hook)?;
    let Ok(Some((left, right))) = read_operands(hook, arguments) else {
        return None;
    };
    MixedPair::of(left, right)
}

#[derive(Clone, Copy)]
enum Comparison {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
}

impl KFloat {
    fn parse(hook: &str, token: &str) -> HookResult<Self> {
        if !is_float_syntax(token) {
            return Err(invalid_token(hook, token).into());
        }
        let (text, precision, exponent_bits) = parse_parts(hook, token)?;
        match (precision, exponent_bits) {
            (24, 8) => parse_f32(text)
                .map(Self::Binary32)
                .ok_or_else(|| invalid_token(hook, token))
                .map_err(Into::into),
            (53, 11) => parse_f64(text)
                .map(Self::Binary64)
                .ok_or_else(|| invalid_token(hook, token))
                .map_err(Into::into),
            _ => Err(BuiltinError::UnsupportedFloatFormat {
                hook: hook.into(),
                precision,
                exponent_bits,
            }
            .into()),
        }
    }

    fn precision(self) -> u32 {
        match self {
            Self::Binary32(_) => 24,
            Self::Binary64(_) => 53,
        }
    }

    fn exponent_bits(self) -> u32 {
        match self {
            Self::Binary32(_) => 8,
            Self::Binary64(_) => 11,
        }
    }

    fn is_sign_negative(self) -> bool {
        match self {
            Self::Binary32(value) => value.is_sign_negative(),
            Self::Binary64(value) => value.is_sign_negative(),
        }
    }

    fn is_nan(self) -> bool {
        match self {
            Self::Binary32(value) => value.is_nan(),
            Self::Binary64(value) => value.is_nan(),
        }
    }

    fn neg(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(-value),
            Self::Binary64(value) => Self::Binary64(-value),
        }
    }

    fn abs(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(value.abs()),
            Self::Binary64(value) => Self::Binary64(value.abs()),
        }
    }

    fn floor(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(value.floor()),
            Self::Binary64(value) => Self::Binary64(value.floor()),
        }
    }

    fn ceil(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(value.ceil()),
            Self::Binary64(value) => Self::Binary64(value.ceil()),
        }
    }

    fn trunc(self) -> Self {
        match self {
            Self::Binary32(value) => Self::Binary32(value.trunc()),
            Self::Binary64(value) => Self::Binary64(value.trunc()),
        }
    }

    /// `rootFloat(x, n)`, "the Nth integer root": IEEE 754 `rootn(x, n)` rounded to nearest in
    /// `x`'s format ([`root`](mod@root)). Its special cases (`n = 0`, a NaN, a zero, an infinity, a negative
    /// `x` with an even `n`) are IEEE's; degree 1 is `x`, degree -1 the IEEE division `1/x`,
    /// degree 2 IEEE `squareRoot` (the even root of -0 being +0, so `sqrtFloat(-0.0)`, the K rule
    /// `rootFloat(F, 2)`, is +0), and every other degree is rounded exactly.
    fn root(self, degree: &BigInt) -> Self {
        match self {
            Self::Binary32(value) => {
                Self::Binary32(match root::special_root(f64::from(value), degree) {
                    Some(special) => special as f32,
                    None => match root::native_degree(degree) {
                        Some(1) => value,
                        Some(-1) => 1.0 / value,
                        Some(_) => value.sqrt(),
                        None => f32::from_bits(
                            u32::try_from(root::positive_root_bits(
                                root::BINARY32,
                                u64::from(value.abs().to_bits()),
                                degree,
                            ))
                            .expect("a binary32 bit pattern"),
                        )
                        .copysign(value),
                    },
                })
            }
            Self::Binary64(value) => Self::Binary64(match root::special_root(value, degree) {
                Some(special) => special,
                None => match root::native_degree(degree) {
                    Some(1) => value,
                    Some(-1) => 1.0 / value,
                    Some(_) => value.sqrt(),
                    None => f64::from_bits(root::positive_root_bits(
                        root::BINARY64,
                        value.abs().to_bits(),
                        degree,
                    ))
                    .copysign(value),
                },
            }),
        }
    }

    /// The exact result of `operation` rounded once to nearest, ties to even, in the destination
    /// format: the operands' format when they share one, and otherwise the operand format that
    /// contains the other, binary64 ([`MixedPair`]). The second is k-rust's reading, which the
    /// root evaluation outside an execution withholds (`super::implementation_chosen`).
    ///
    /// A value is computed only when both operands are binary32 or binary64: an operand of any
    /// other format is refused by `read_float` (`UnsupportedFloatFormat`) before this, and is never
    /// read as binary32 or binary64.
    fn binary(self, other: Self, operation: BinaryOperation) -> Self {
        match (self, other) {
            (Self::Binary32(left), Self::Binary32(right)) => {
                Self::Binary32(operation.binary32(left, right))
            }
            (Self::Binary64(left), Self::Binary64(right)) => {
                Self::Binary64(operation.binary64(left, right))
            }
            // The pairs `MixedPair::of` names, spelled out so that a further format is a build
            // error here rather than a pair this arm would read as binary32 and binary64.
            (Self::Binary32(_), Self::Binary64(_)) | (Self::Binary64(_), Self::Binary32(_)) => {
                let (left, right) = MixedPair {
                    left: self,
                    right: other,
                }
                .widened();
                Self::Binary64(operation.binary64(left, right))
            }
        }
    }

    /// Whether the comparison holds of the exact values. A truth value has no format, so values
    /// of two formats are compared as they are (IEEE 754-2008 5.11), in every evaluation mode:
    /// both widen exactly to binary64.
    fn compare(self, other: Self, comparison: Comparison) -> bool {
        let left = self.as_f64();
        let right = other.as_f64();
        match comparison {
            Comparison::Less => left < right,
            Comparison::LessEqual => left <= right,
            Comparison::Greater => left > right,
            Comparison::GreaterEqual => left >= right,
            Comparison::Equal => left == right,
        }
    }

    fn as_f64(self) -> f64 {
        match self {
            Self::Binary32(value) => f64::from(value),
            Self::Binary64(value) => value,
        }
    }

    fn round_to(self, precision: u32, exponent_bits: u32) -> Self {
        match (precision, exponent_bits) {
            (24, 8) => Self::Binary32(match self {
                Self::Binary32(value) => value,
                Self::Binary64(value) => value as f32,
            }),
            (53, 11) => Self::Binary64(self.as_f64()),
            _ => unreachable!("the requested Float format was validated"),
        }
    }

    fn round_to_integer(self) -> Option<BigInt> {
        let rounded = match self {
            Self::Binary32(value) => f64::from(value.round_ties_even()),
            Self::Binary64(value) => value.round_ties_even(),
        };
        BigInt::from_f64(rounded)
    }

    fn token(self) -> String {
        match self {
            Self::Binary32(value) => canonical_f32(value),
            Self::Binary64(value) => canonical_f64(value),
        }
    }
}

pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    match hook {
        "FLOAT.precision" => inspect(hook, arguments, |value| {
            int_term(BigInt::from(value.precision()))
        }),
        "FLOAT.exponentBits" => inspect(hook, arguments, |value| {
            int_term(BigInt::from(value.exponent_bits()))
        }),
        "FLOAT.sign" => inspect(hook, arguments, |value| bool_term(value.is_sign_negative())),
        "FLOAT.isNaN" => inspect(hook, arguments, |value| bool_term(value.is_nan())),
        "FLOAT.neg" => inspect(hook, arguments, |value| float_term(value.neg())),
        "FLOAT.abs" => inspect(hook, arguments, |value| float_term(value.abs())),
        "FLOAT.floor" => inspect(hook, arguments, |value| float_term(value.floor())),
        "FLOAT.ceil" => inspect(hook, arguments, |value| float_term(value.ceil())),
        "FLOAT.trunc" => inspect(hook, arguments, |value| float_term(value.trunc())),
        "FLOAT.root" => root(hook, arguments),
        "FLOAT.add" | "FLOAT.sub" | "FLOAT.mul" | "FLOAT.div" | "FLOAT.min" | "FLOAT.max" => {
            let operation = BinaryOperation::of(hook).expect("a binary Float operation");
            binary(hook, arguments, operation)
        }
        "FLOAT.lt" => compare(hook, arguments, Comparison::Less),
        "FLOAT.le" => compare(hook, arguments, Comparison::LessEqual),
        "FLOAT.gt" => compare(hook, arguments, Comparison::Greater),
        "FLOAT.ge" => compare(hook, arguments, Comparison::GreaterEqual),
        "FLOAT.eq" => compare(hook, arguments, Comparison::Equal),
        "FLOAT.round" => round(hook, arguments),
        "FLOAT.int2float" => int_to_float(hook, arguments),
        "FLOAT.float2int" => float_to_int(hook, arguments),
        "FLOAT.maxValue" => maximum_value(hook, arguments),
        _ => Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        )),
    }
}

fn root(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 2)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(degree) = read_int(&arguments[1]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(float_term(value.root(&degree))))
}

fn round(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 3)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((precision, exponent_bits)) = read_format(hook, &arguments[1], &arguments[2])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(float_term(
        value.round_to(precision, exponent_bits),
    )))
}

fn int_to_float(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 3)?;
    let Some(integer) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some((precision, exponent_bits)) = read_format(hook, &arguments[1], &arguments[2])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let value = match (precision, exponent_bits) {
        (24, 8) => KFloat::Binary32(
            integer
                .to_f32()
                .expect("num-bigint defines binary32 conversion for every BigInt"),
        ),
        (53, 11) => KFloat::Binary64(
            integer
                .to_f64()
                .expect("num-bigint defines binary64 conversion for every BigInt"),
        ),
        _ => unreachable!("the requested Float format was validated"),
    };
    Ok(BuiltinResult::Value(float_term(value)))
}

fn float_to_int(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 1)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    // `Float2Int` is total; NaN and the infinities have no nearest integer, so the definition
    // does not give its value there.
    Ok(value.round_to_integer().map_or_else(
        || {
            BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified {
                defined: false,
                detail: "Float2Int of NaN or an infinity, which has no nearest integer".into(),
            })
        },
        |integer| BuiltinResult::Value(int_term(integer)),
    ))
}

fn maximum_value(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 2)?;
    let Some((precision, exponent_bits)) = read_format(hook, &arguments[0], &arguments[1])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let value = match (precision, exponent_bits) {
        (24, 8) => KFloat::Binary32(f32::MAX),
        (53, 11) => KFloat::Binary64(f64::MAX),
        _ => unreachable!("the requested Float format was validated"),
    };
    Ok(BuiltinResult::Value(float_term(value)))
}

fn read_format(
    hook: &str,
    precision: &Term,
    exponent_bits: &Term,
) -> HookResult<Option<(u32, u32)>> {
    let Some(precision) = read_int(precision) else {
        return Ok(None);
    };
    let Some(exponent_bits) = read_int(exponent_bits) else {
        return Ok(None);
    };
    let (Some(precision_u32), Some(exponent_bits_u32)) =
        (precision.to_u32(), exponent_bits.to_u32())
    else {
        return Err(BuiltinError::UnsupportedFloatFormatParameters {
            hook: hook.into(),
            precision: precision.to_string(),
            exponent_bits: exponent_bits.to_string(),
        }
        .into());
    };
    match (precision_u32, exponent_bits_u32) {
        (24, 8) | (53, 11) => Ok(Some((precision_u32, exponent_bits_u32))),
        _ => Err(BuiltinError::UnsupportedFloatFormat {
            hook: hook.into(),
            precision: precision_u32,
            exponent_bits: exponent_bits_u32,
        }
        .into()),
    }
}

/// The two Float operands of a binary hook, as every binary Float evaluator and
/// [`mixed_destination`] read them; `None` while either is not a Float domain value.
fn read_operands(hook: &str, arguments: &[Term]) -> HookResult<Option<(KFloat, KFloat)>> {
    expect_arity(hook, arguments, 2)?;
    let Some(left) = read_float(hook, &arguments[0])? else {
        return Ok(None);
    };
    let Some(right) = read_float(hook, &arguments[1])? else {
        return Ok(None);
    };
    Ok(Some((left, right)))
}

fn binary(hook: &str, arguments: &[Term], operation: BinaryOperation) -> HookResult<BuiltinResult> {
    let Some((left, right)) = read_operands(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(float_term(
        left.binary(right, operation),
    )))
}

fn compare(hook: &str, arguments: &[Term], comparison: Comparison) -> HookResult<BuiltinResult> {
    let Some((left, right)) = read_operands(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(bool_term(
        left.compare(right, comparison),
    )))
}

fn inspect(
    hook: &str,
    arguments: &[Term],
    operation: impl FnOnce(KFloat) -> Term,
) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 1)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(BuiltinResult::Value(operation(value)))
}

fn read_float(hook: &str, term: &Term) -> HookResult<Option<KFloat>> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return Ok(None);
    };
    if !sort.is_builtin(BuiltinSort::Float) {
        return Ok(None);
    }
    let Ok(value) = value.as_utf8() else {
        return Ok(None);
    };
    KFloat::parse(hook, value).map(Some)
}

/// A `Float` value of the hooks, at `SortFloat`. Its kind is the one the definition gives a sort
/// hooked `FLOAT.Float`, `Token` until Float values have a kind of their own; the evaluation
/// entry compares it with the kind the definition gives `SortFloat`.
fn float_term(value: KFloat) -> Term {
    Term::domain_value_of(
        DomainKind::Token,
        Sort::builtin(BuiltinSort::Float),
        value.token(),
    )
}

/// Whether `token` is in the lexical syntax of the `Float` sort (`domains.md`, FLOAT-SYNTAX):
/// `[+-]?[0-9]+(.[0-9]*)?` or `.[0-9]+` with an optional exponent, `[+-]?Infinity`, or `NaN`,
/// each with an optional `f`/`d` or `p<digits>x<digits>` suffix. A Float domain value denotes the
/// element its string names in that syntax, so a string outside it (`inf`, `-.5`, ` 1.0`) names
/// none, although general float parsers accept such spellings.
pub fn is_float_syntax(token: &str) -> bool {
    let digits = |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
    let body = match token
        .rsplit_once(['x', 'X'])
        .and_then(|(rest, exponent_bits)| Some((rest.rsplit_once(['p', 'P'])?, exponent_bits)))
    {
        Some(((body, precision), exponent_bits)) if digits(precision) && digits(exponent_bits) => {
            body
        }
        _ => token.strip_suffix(['f', 'F', 'd', 'D']).unwrap_or(token),
    };
    if body == "NaN" || body.strip_prefix(['+', '-']).unwrap_or(body) == "Infinity" {
        return true;
    }
    let (mantissa, exponent) = match body.split_once(['e', 'E']) {
        Some((mantissa, exponent)) => (mantissa, Some(exponent)),
        None => (body, None),
    };
    let exponent_ok = exponent
        .is_none_or(|exponent| digits(exponent.strip_prefix(['+', '-']).unwrap_or(exponent)));
    let mantissa_ok = match mantissa.strip_prefix('.') {
        Some(fraction) => digits(fraction),
        None => {
            let unsigned = mantissa.strip_prefix(['+', '-']).unwrap_or(mantissa);
            match unsigned.split_once('.') {
                Some((whole, fraction)) => {
                    digits(whole) && (fraction.is_empty() || digits(fraction))
                }
                None => digits(unsigned),
            }
        }
    };
    mantissa_ok && exponent_ok
}

fn parse_parts<'a>(hook: &str, token: &'a str) -> HookResult<(&'a str, u32, u32)> {
    if let Some((value_and_precision, exponent)) = token.rsplit_once(['x', 'X'])
        && let Some((value, precision)) = value_and_precision.rsplit_once(['p', 'P'])
    {
        let precision = precision.parse().map_err(|_| invalid_token(hook, token))?;
        let exponent_bits = exponent.parse().map_err(|_| invalid_token(hook, token))?;
        return Ok((value, precision, exponent_bits));
    }
    if let Some(value) = token.strip_suffix(['f', 'F']) {
        Ok((value, 24, 8))
    } else {
        Ok((token.strip_suffix(['d', 'D']).unwrap_or(token), 53, 11))
    }
}

fn parse_f32(text: &str) -> Option<f32> {
    match text {
        "Infinity" => Some(f32::INFINITY),
        "-Infinity" => Some(f32::NEG_INFINITY),
        "NaN" => Some(f32::NAN),
        _ => text.parse().ok(),
    }
}

fn parse_f64(text: &str) -> Option<f64> {
    match text {
        "Infinity" => Some(f64::INFINITY),
        "-Infinity" => Some(f64::NEG_INFINITY),
        "NaN" => Some(f64::NAN),
        _ => text.parse().ok(),
    }
}

fn invalid_token(hook: &str, token: &str) -> BuiltinError {
    BuiltinError::InvalidFloatToken {
        hook: hook.into(),
        token: token.into(),
    }
}

fn canonical_f32(value: f32) -> String {
    canonical(
        value.is_nan(),
        value.is_infinite(),
        value.is_sign_negative(),
        value == 0.0,
        (!value.is_nan() && !value.is_infinite() && value != 0.0).then(|| format!("{value:.8e}")),
        24,
        8,
    )
}

fn canonical_f64(value: f64) -> String {
    canonical(
        value.is_nan(),
        value.is_infinite(),
        value.is_sign_negative(),
        value == 0.0,
        (!value.is_nan() && !value.is_infinite() && value != 0.0).then(|| format!("{value:.16e}")),
        53,
        11,
    )
}

fn canonical(
    is_nan: bool,
    is_infinite: bool,
    is_sign_negative: bool,
    is_zero: bool,
    finite: Option<String>,
    precision: u32,
    exponent_bits: u32,
) -> String {
    let value = if is_nan {
        "NaN".into()
    } else if is_infinite {
        if is_sign_negative {
            "-Infinity"
        } else {
            "Infinity"
        }
        .into()
    } else if is_zero {
        if is_sign_negative { "-0e+00" } else { "0e+00" }.into()
    } else {
        normalize_exponent(finite.expect("finite nonzero Floats have decimal text"))
    };
    format!("{value}p{precision}x{exponent_bits}")
}

fn normalize_exponent(scientific: String) -> String {
    let (mantissa, exponent) = scientific
        .split_once('e')
        .expect("Rust scientific Float formatting includes an exponent");
    let exponent = exponent
        .parse::<i32>()
        .expect("Rust scientific Float formatting uses a decimal exponent");
    format!("{mantissa}e{exponent:+03}")
}

fn minimum_f32(left: f32, right: f32) -> f32 {
    if left.is_nan() {
        right
    } else if right.is_nan() || left < right {
        left
    } else if right < left {
        right
    } else if left == 0.0 && (left.is_sign_negative() || right.is_sign_negative()) {
        -0.0
    } else {
        left
    }
}

fn maximum_f32(left: f32, right: f32) -> f32 {
    if left.is_nan() {
        right
    } else if right.is_nan() || left > right {
        left
    } else if right > left {
        right
    } else if left == 0.0 && (!left.is_sign_negative() || !right.is_sign_negative()) {
        0.0
    } else {
        left
    }
}

fn minimum_f64(left: f64, right: f64) -> f64 {
    if left.is_nan() {
        right
    } else if right.is_nan() || left < right {
        left
    } else if right < left {
        right
    } else if left == 0.0 && (left.is_sign_negative() || right.is_sign_negative()) {
        -0.0
    } else {
        left
    }
}

fn maximum_f64(left: f64, right: f64) -> f64 {
    if left.is_nan() {
        right
    } else if right.is_nan() || left > right {
        left
    } else if right > left {
        right
    } else if left == 0.0 && (!left.is_sign_negative() || !right.is_sign_negative()) {
        0.0
    } else {
        left
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn float(token: &str) -> Term {
        Term::raw_domain_value(Sort::builtin(BuiltinSort::Float), token)
    }

    /// `mixed_destination` names exactly the pairs the evaluator reads as one binary32 and one
    /// binary64 operand: every spelling of each format, in both orders, for the six Float-valued
    /// binary hooks; not one format, not a comparison, not a symbolic operand, and not a format
    /// the evaluator does not read.
    #[test]
    fn mixed_destination_names_exactly_the_pairs_the_evaluator_widens() {
        let binary32 = ["0.1f", "0.1F", "0.1p24x8", "0.1p024x008", "0.1P24X8"];
        let binary64 = ["2.0", "2.0d", "2.0D", "2.0p53x11", "2.0p053x0011"];
        let hooks = [
            "FLOAT.add",
            "FLOAT.sub",
            "FLOAT.mul",
            "FLOAT.div",
            "FLOAT.min",
            "FLOAT.max",
        ];
        for hook in hooks {
            for single in binary32 {
                for double in binary64 {
                    for (left, right) in [(single, double), (double, single)] {
                        let arguments = [float(left), float(right)];
                        assert!(
                            mixed_destination(hook, &arguments).is_some(),
                            "{hook}({left}, {right})"
                        );
                        let Ok(BuiltinResult::Value(value)) = evaluate(hook, &arguments) else {
                            panic!("{hook}({left}, {right}) has a value");
                        };
                        let TermKind::DomainValue { value, .. } = value.kind() else {
                            panic!("{hook}({left}, {right}) is a domain value");
                        };
                        assert!(
                            value.as_utf8().unwrap().ends_with("p53x11"),
                            "{hook}({left}, {right})"
                        );
                    }
                }
            }
            for (left, right) in [("0.1f", "2.0p24x8"), ("0.1", "2.0p53x11")] {
                assert!(
                    mixed_destination(hook, &[float(left), float(right)]).is_none(),
                    "{hook}({left}, {right})"
                );
            }
            let variable = Term::variable(crate::term::Variable::new(
                "X",
                Sort::builtin(BuiltinSort::Float),
            ));
            assert!(mixed_destination(hook, &[float("0.1f"), variable]).is_none());
            assert!(mixed_destination(hook, &[float("0.1f"), float("2.0p113x15")]).is_none());
        }
        for hook in ["FLOAT.lt", "FLOAT.eq", "FLOAT.rem", "FLOAT.pow"] {
            assert!(mixed_destination(hook, &[float("0.1f"), float("2.0")]).is_none());
        }
    }
}
