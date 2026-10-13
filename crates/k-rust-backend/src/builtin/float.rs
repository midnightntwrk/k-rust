//! Portable IEEE binary32/binary64 implementations of K's `FLOAT` hooks.

use std::fmt;

use num_bigint::{BigInt, BigUint};
use num_traits::{FromPrimitive, One, Signed, ToPrimitive, Zero};

use k_rust_kore::names::BuiltinSort;

use super::{
    BuiltinError, BuiltinResult, HookResult, UnsupportedHookReason, bool_term, expect_arity,
    int_term, read_int,
};
use crate::term::{DomainKind, Sort, Term, TermKind};

mod canonical;
mod root;

pub use canonical::{
    FloatTextRefusal, MAX_FLOAT_CANONICAL_BITS, canonical_float_text, float_canonical_bits_estimate,
};

#[derive(Clone, Copy, Debug)]
enum KFloat {
    Binary32(f32),
    Binary64(f64),
}

/// A Float format `pNxM`: `N` bits of precision and `M` exponent bits, both positive integers
/// (`domains.md`, "Floating-point numbers"). The fields are compared as numbers, so `p053x011`
/// is binary64. The backend computes binary32 (`p24x8`) and binary64 (`p53x11`); the definition
/// gives values in every other format too, which this backend does not compute.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FloatFormat {
    pub(super) precision: BigUint,
    pub(super) exponent_bits: BigUint,
}

impl FloatFormat {
    /// The format of these fields; `None` when either is 0, which names no format.
    fn new(precision: BigUint, exponent_bits: BigUint) -> Option<Self> {
        (!precision.is_zero() && !exponent_bits.is_zero()).then_some(Self {
            precision,
            exponent_bits,
        })
    }

    fn of(precision: u32, exponent_bits: u32) -> Self {
        Self {
            precision: precision.into(),
            exponent_bits: exponent_bits.into(),
        }
    }

    fn is(&self, precision: u32, exponent_bits: u32) -> bool {
        self.precision == BigUint::from(precision)
            && self.exponent_bits == BigUint::from(exponent_bits)
    }

    pub(super) fn is_binary32(&self) -> bool {
        self.is(24, 8)
    }

    pub(super) fn is_binary64(&self) -> bool {
        self.is(53, 11)
    }

    fn is_computed(&self) -> bool {
        self.is_binary32() || self.is_binary64()
    }

    /// A field of 1: a format without IEEE-like parameters (no trailing significand bit, or
    /// `emin > emax`), which this backend does not compute even from the suffix.
    pub(super) fn has_a_field_of_one(&self) -> bool {
        self.precision.is_one() || self.exponent_bits.is_one()
    }

    /// Whether every value of `other` is a value of this format: at least its precision and its
    /// exponent range.
    fn contains(&self, other: &Self) -> bool {
        self.precision >= other.precision && self.exponent_bits >= other.exponent_bits
    }
}

impl fmt::Display for FloatFormat {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "p{}x{} (precision {}, {} exponent bits)",
            self.precision, self.exponent_bits, self.precision, self.exponent_bits
        )
    }
}

/// The body of `token`, a text in FLOAT-SYNTAX ([`is_float_syntax`]), and the format its suffix
/// names: none, `d` or `D` is binary64, `f` or `F` binary32, and `pNxM` the format `pNxM`, its
/// fields read as unbounded integers; `None` for the format when a field is 0, which names no
/// format, so the token names no Float.
pub(super) fn split_token(token: &str) -> (&str, Option<FloatFormat>) {
    let digits = |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
    let explicit = token
        .rsplit_once(['x', 'X'])
        .and_then(|(rest, exponent_bits)| Some((rest.rsplit_once(['p', 'P'])?, exponent_bits)))
        .filter(|((_, precision), exponent_bits)| digits(precision) && digits(exponent_bits));
    match explicit {
        Some(((body, precision), exponent_bits)) => (
            body,
            FloatFormat::new(
                precision.parse().expect("decimal digits"),
                exponent_bits.parse().expect("decimal digits"),
            ),
        ),
        None => match token.strip_suffix(['f', 'F']) {
            Some(body) => (body, Some(FloatFormat::of(24, 8))),
            None => (
                token.strip_suffix(['d', 'D']).unwrap_or(token),
                Some(FloatFormat::of(53, 11)),
            ),
        },
    }
}

/// A Float argument as the evaluator reads it.
#[derive(Clone, Debug)]
enum Operand<'a> {
    /// A binary32 or binary64 value.
    Computed(KFloat),
    /// A value of another format, which this backend does not compute: the token's body in
    /// FLOAT-SYNTAX (a sign and a magnitude, or `NaN`) and its format.
    Uncomputed { body: &'a str, format: FloatFormat },
}

impl Operand<'_> {
    fn format(&self) -> FloatFormat {
        match self {
            Self::Computed(value) => value.format(),
            Self::Uncomputed { format, .. } => format.clone(),
        }
    }
}

/// What a pair of format arguments (`roundFloat`, `Int2Float`, `maxValueFloat`) names.
enum FormatArguments {
    /// A field of zero or below: no format, so the application is undefined.
    NoFormat,
    /// A field is not an integer value yet, and neither known field is zero or below.
    Symbolic,
    Format(FloatFormat),
}

/// The detail of the unsupported-hook outcome of `hook` applied to Floats of `formats`, the
/// formats the backend does not compute: the definition gives the application a value, which
/// this backend does not evaluate.
fn uncomputed_operands(hook: &str, formats: &[&FloatFormat]) -> BuiltinResult {
    let named = match formats {
        [format] => format!("a Float of the format {format}"),
        _ => format!(
            "Floats of the formats {}",
            formats
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" and ")
        ),
    };
    out_of_range(format!(
        "this backend does not evaluate {hook} on {named}; it evaluates {hook} on binary32 \
         (p24x8) and binary64 (p53x11) Floats only"
    ))
}

/// The detail of the unsupported-hook outcome of `hook` rounding to `format`, a format the
/// backend does not compute.
fn uncomputed_destination(hook: &str, format: &FloatFormat) -> BuiltinResult {
    out_of_range(format!(
        "this backend does not evaluate {hook} to the format {format}; it evaluates {hook} to \
         binary32 (p24x8) and binary64 (p53x11) only"
    ))
}

fn out_of_range(detail: String) -> BuiltinResult {
    BuiltinResult::Unsupported(UnsupportedHookReason::ArgumentOutOfRange { detail })
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
    let Ok(Some((Operand::Computed(left), Operand::Computed(right)))) =
        read_operands(hook, arguments)
    else {
        return None;
    };
    MixedPair::of(left, right)
}

/// Why `signFloat` applied to `arguments` reads a value the definition leaves open, when its
/// argument is a NaN of any format; `None` otherwise.
///
/// `signFloat` is "the value of the sign bit" of a `Float`, a value of an IEEE-like format, in
/// which every value, a NaN included, has a sign bit; the literal `NaN` names a NaN without
/// saying which of the two it has. The description therefore gives the application a Bool value
/// in every model, whatever its declaration says, but which one the definition does not
/// determine: the evaluator's `false` is k-rust's reading, applied only in an execution
/// (`super::implementation_chosen`). The argument is read exactly as the evaluator reads it.
pub(crate) fn nan_sign(hook: &str, arguments: &[Term]) -> Option<String> {
    if hook != "FLOAT.sign" {
        return None;
    }
    let [argument] = arguments else {
        return None;
    };
    let nan = match read_float(hook, argument) {
        Ok(Some(Operand::Computed(value))) => value.is_nan(),
        Ok(Some(Operand::Uncomputed { body, .. })) => body == "NaN",
        Ok(None) | Err(_) => false,
    };
    nan.then(|| {
        "FLOAT.sign of a NaN reads a sign bit the NaN literal is not given; k-rust's reading, \
         false, applies only in an execution"
            .into()
    })
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
    /// The Float `token` names: a binary32 or binary64 value, or the body and format of a
    /// value of another format, which is never read as binary32 or binary64. A text outside
    /// FLOAT-SYNTAX, or whose suffix has a field of 0, names no Float (`InvalidFloatToken`).
    fn parse<'a>(hook: &str, token: &'a str) -> HookResult<Operand<'a>> {
        if !is_float_syntax(token) {
            return Err(invalid_token(hook, token).into());
        }
        let (body, Some(format)) = split_token(token) else {
            return Err(invalid_token(hook, token).into());
        };
        let value = if format.is_binary32() {
            parse_f32(body).map(Self::Binary32)
        } else if format.is_binary64() {
            parse_f64(body).map(Self::Binary64)
        } else {
            return Ok(Operand::Uncomputed { body, format });
        };
        value
            .map(Operand::Computed)
            .ok_or_else(|| invalid_token(hook, token).into())
    }

    fn format(self) -> FloatFormat {
        FloatFormat::of(self.precision(), self.exponent_bits())
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
    /// other format is the unsupported-hook outcome (`binary`) before this, and is never read as
    /// binary32 or binary64.
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

    /// The value rounded to `format`, binary32 or binary64.
    fn round_to(self, format: &FloatFormat) -> Self {
        if format.is_binary32() {
            Self::Binary32(match self {
                Self::Binary32(value) => value,
                Self::Binary64(value) => value as f32,
            })
        } else {
            debug_assert!(
                format.is_binary64(),
                "the requested Float format was validated"
            );
            Self::Binary64(self.as_f64())
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
        "FLOAT.precision" => from_token(
            hook,
            arguments,
            |value| int_term(BigInt::from(value.precision())),
            |_, format| int_term(format.precision.clone().into()),
        ),
        "FLOAT.exponentBits" => from_token(
            hook,
            arguments,
            |value| int_term(BigInt::from(value.exponent_bits())),
            |_, format| int_term(format.exponent_bits.clone().into()),
        ),
        // Rounding to nearest never changes a sign (a negative literal that underflows is -0),
        // and the only NaN literal is `NaN`, without a sign.
        "FLOAT.sign" => from_token(
            hook,
            arguments,
            |value| bool_term(value.is_sign_negative()),
            |body, _| bool_term(body.starts_with('-')),
        ),
        "FLOAT.isNaN" => from_token(
            hook,
            arguments,
            |value| bool_term(value.is_nan()),
            |body, _| bool_term(body == "NaN"),
        ),
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
    let value = match value {
        Operand::Computed(value) => value,
        Operand::Uncomputed { format, .. } => return Ok(uncomputed_operands(hook, &[&format])),
    };
    Ok(BuiltinResult::Value(float_term(value.root(&degree))))
}

/// `roundFloat(F, P, E)`. The format arguments are read first: where they name no format the
/// application is undefined whatever `F` is.
fn round(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 3)?;
    let format = match read_format(&arguments[1], &arguments[2]) {
        FormatArguments::NoFormat => return Ok(BuiltinResult::Bottom),
        FormatArguments::Symbolic => None,
        FormatArguments::Format(format) => Some(format),
    };
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let Some(format) = format else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let value = match value {
        Operand::Computed(value) => value,
        Operand::Uncomputed { format, .. } => return Ok(uncomputed_operands(hook, &[&format])),
    };
    if !format.is_computed() {
        return Ok(uncomputed_destination(hook, &format));
    }
    Ok(BuiltinResult::Value(float_term(value.round_to(&format))))
}

/// `Int2Float(I, P, E)`. The format arguments are read first: where they name no format the
/// application is undefined whatever `I` is.
fn int_to_float(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 3)?;
    let format = match read_format(&arguments[1], &arguments[2]) {
        FormatArguments::NoFormat => return Ok(BuiltinResult::Bottom),
        FormatArguments::Symbolic => return Ok(BuiltinResult::NotApplicable),
        FormatArguments::Format(format) => format,
    };
    let Some(integer) = read_int(&arguments[0]) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let value = if format.is_binary32() {
        KFloat::Binary32(
            integer
                .to_f32()
                .expect("num-bigint defines binary32 conversion for every BigInt"),
        )
    } else if format.is_binary64() {
        KFloat::Binary64(
            integer
                .to_f64()
                .expect("num-bigint defines binary64 conversion for every BigInt"),
        )
    } else {
        return Ok(uncomputed_destination(hook, &format));
    };
    Ok(BuiltinResult::Value(float_term(value)))
}

fn float_to_int(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 1)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    // `Float2Int` is total; NaN and the infinities have no nearest integer, in any format, so
    // the definition does not give its value there. In a format the backend does not compute
    // they are named by the token's body alone, as `isNaN` reads it.
    let no_nearest_integer = || {
        BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified {
            defined: false,
            detail: "Float2Int of NaN or an infinity, which has no nearest integer".into(),
        })
    };
    let value = match value {
        Operand::Computed(value) => value,
        Operand::Uncomputed { body, .. }
            if body == "NaN" || body.strip_prefix(['+', '-']).unwrap_or(body) == "Infinity" =>
        {
            return Ok(no_nearest_integer());
        }
        Operand::Uncomputed { format, .. } => return Ok(uncomputed_operands(hook, &[&format])),
    };
    Ok(value
        .round_to_integer()
        .map_or_else(no_nearest_integer, |integer| {
            BuiltinResult::Value(int_term(integer))
        }))
}

fn maximum_value(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 2)?;
    let format = match read_format(&arguments[0], &arguments[1]) {
        FormatArguments::NoFormat => return Ok(BuiltinResult::Bottom),
        FormatArguments::Symbolic => return Ok(BuiltinResult::NotApplicable),
        FormatArguments::Format(format) => format,
    };
    let value = if format.is_binary32() {
        KFloat::Binary32(f32::MAX)
    } else if format.is_binary64() {
        KFloat::Binary64(f64::MAX)
    } else {
        return Ok(uncomputed_destination(hook, &format));
    };
    Ok(BuiltinResult::Value(float_term(value)))
}

/// The format a precision and an exponent-bits argument name. A field of zero or below names
/// no format (`domains.md` requires positive integers), whatever the other field is; any two
/// positive fields name one, however large.
fn read_format(precision: &Term, exponent_bits: &Term) -> FormatArguments {
    let (precision, exponent_bits) = (read_int(precision), read_int(exponent_bits));
    if [&precision, &exponent_bits]
        .into_iter()
        .flatten()
        .any(|field| !field.is_positive())
    {
        return FormatArguments::NoFormat;
    }
    let (Some(precision), Some(exponent_bits)) = (precision, exponent_bits) else {
        return FormatArguments::Symbolic;
    };
    FormatArguments::Format(FloatFormat {
        precision: precision.magnitude().clone(),
        exponent_bits: exponent_bits.magnitude().clone(),
    })
}

/// The two Float operands of a binary hook, as every binary Float evaluator and
/// [`mixed_destination`] read them; `None` while either is not a Float domain value.
fn read_operands<'a>(
    hook: &str,
    arguments: &'a [Term],
) -> HookResult<Option<(Operand<'a>, Operand<'a>)>> {
    expect_arity(hook, arguments, 2)?;
    let Some(left) = read_float(hook, &arguments[0])? else {
        return Ok(None);
    };
    let Some(right) = read_float(hook, &arguments[1])? else {
        return Ok(None);
    };
    Ok(Some((left, right)))
}

/// The unsupported-hook outcome of a binary operation over `left` and `right`, at least one of
/// a format the backend does not compute. Over one format that format is the result's; over
/// two, the result's format is the operand format that contains the other (the reading binary32
/// and binary64 operands take, [`MixedPair`]), and an operand of a format the backend does not
/// compute cannot be read even where the result's format is binary64. Where neither format
/// contains the other no operand format is the result's.
fn uncomputed_pair(hook: &str, left: &FloatFormat, right: &FloatFormat) -> BuiltinResult {
    if left != right && !left.contains(right) && !right.contains(left) {
        return out_of_range(format!(
            "this backend does not evaluate {hook} on Floats of the formats {left} and {right}: \
             neither format contains the other, so neither is the result's format; it evaluates \
             {hook} on binary32 (p24x8) and binary64 (p53x11) Floats only"
        ));
    }
    uncomputed_operands_of(hook, left, right)
}

/// [`uncomputed_operands`] naming those of `left` and `right` the backend does not compute.
fn uncomputed_operands_of(hook: &str, left: &FloatFormat, right: &FloatFormat) -> BuiltinResult {
    let mut formats = vec![left];
    if right != left {
        formats.push(right);
    }
    formats.retain(|format| !format.is_computed());
    uncomputed_operands(hook, &formats)
}

fn binary(hook: &str, arguments: &[Term], operation: BinaryOperation) -> HookResult<BuiltinResult> {
    let Some((left, right)) = read_operands(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let (Operand::Computed(left), Operand::Computed(right)) = (&left, &right) else {
        return Ok(uncomputed_pair(hook, &left.format(), &right.format()));
    };
    Ok(BuiltinResult::Value(float_term(
        left.binary(*right, operation),
    )))
}

/// A comparison has a value over any two formats, so an operand of a format the backend does not
/// compute is the unsupported-hook outcome naming it.
fn compare(hook: &str, arguments: &[Term], comparison: Comparison) -> HookResult<BuiltinResult> {
    let Some((left, right)) = read_operands(hook, arguments)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let (Operand::Computed(left), Operand::Computed(right)) = (&left, &right) else {
        return Ok(uncomputed_operands_of(
            hook,
            &left.format(),
            &right.format(),
        ));
    };
    Ok(BuiltinResult::Value(bool_term(
        left.compare(*right, comparison),
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
    match value {
        Operand::Computed(value) => Ok(BuiltinResult::Value(operation(value))),
        Operand::Uncomputed { format, .. } => Ok(uncomputed_operands(hook, &[&format])),
    }
}

/// A hook whose value is read from the token alone, on every format: from a binary32 or binary64
/// value by `computed`, and from the body and format of a value of another format by
/// `uncomputed`, without reading its magnitude. A format with a field of 1 is not computed even
/// here (`FloatFormat::has_a_field_of_one`).
fn from_token(
    hook: &str,
    arguments: &[Term],
    computed: impl FnOnce(KFloat) -> Term,
    uncomputed: impl FnOnce(&str, &FloatFormat) -> Term,
) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 1)?;
    let Some(value) = read_float(hook, &arguments[0])? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    Ok(match value {
        Operand::Computed(value) => BuiltinResult::Value(computed(value)),
        Operand::Uncomputed { format, .. } if format.has_a_field_of_one() => out_of_range(format!(
            "this backend does not evaluate {hook} on a Float of the format {format}, whose \
                 precision or exponent-bits field is 1; it evaluates {hook} on every format whose \
                 fields are at least 2"
        )),
        Operand::Uncomputed { body, format } => BuiltinResult::Value(uncomputed(body, &format)),
    })
}

fn read_float<'a>(hook: &str, term: &'a Term) -> HookResult<Option<Operand<'a>>> {
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

/// A `Float` value of the hooks, at `SortFloat`, with the `Float` kind of the `FLOAT` hooks'
/// builtin: the evaluation entry compares it with the kind the definition gives `SortFloat`, so
/// it is a value only where `SortFloat` is hooked `FLOAT.Float`. Its text, `canonical_f32` or
/// `canonical_f64`, is the canonical text of its value by construction, so the canonicalizer is
/// not run again.
fn float_term(value: KFloat) -> Term {
    Term::domain_value_of_canonical(
        DomainKind::Float,
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
