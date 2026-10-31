//! Portable IEEE binary32/binary64 implementations of K's `FLOAT` hooks.

use num_bigint::{BigInt, BigUint};
use num_traits::{FromPrimitive, Signed, ToPrimitive, Zero};

use k_rust_domain::float::{
    FloatFormat, canonical_f32, canonical_f64, is_float_syntax, parse_f32, parse_f64, split_token,
};
use k_rust_kore::names::BuiltinSort;

use super::{
    BuiltinError, BuiltinResult, HookResult, Undefinedness, UnsupportedHookReason, bool_term,
    expect_arity, int_term, read_int,
};
use crate::{
    choice_sampling,
    term::{DomainKind, Sort, Term, TermKind},
};

mod destination;
mod root;

#[derive(Clone, Copy, Debug)]
enum KFloat {
    Binary32(f32),
    Binary64(f64),
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
/// of two formats to the language, so the result is open (class `float-destination`); k-rust's
/// pick, applied only in an execution, which marks it, takes the operand format that contains
/// the other, binary64 (the destination IEEE 754-2008 10.3 gives under `preferredWidthNone`):
/// every binary32 value, subnormals, infinities, signed zeros and NaN included, is a binary64
/// value, so the binary32 operand widens exactly and the result is rounded once.
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

    /// Why the definition leaves `hook`'s value on this pair open, for the unevaluated
    /// application outside an execution.
    pub(crate) fn detail(self, hook: &str) -> String {
        format!(
            "{hook} of a Float of precision {} with {} exponent bits and one of precision {} with \
             {} exponent bits rounds to a result format domains.md does not name; k-rust's \
             pick, binary64, applies only in an execution",
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
/// which every value, a NaN included, has a sign bit. A format has one NaN, which every spelling
/// of `NaN` in that format names, as the canonical text stores it (payloads are not modelled):
/// the literal syntax writes one unsigned `NaN` lexeme per format beside signed zeros and
/// infinities, and `Float2String` round-trips every `Float` through that syntax, so every NaN of
/// a format is that lexeme's value (determined; `docs/compatibility.md`, "Backend scope"). The
/// description does not say which sign bit that NaN has, so only the sign bit is open: it gives
/// the application a Bool value in every model, whatever its declaration says, but which one the
/// definition does not determine (class `nan-sign`): the evaluator's `false` is k-rust's pick,
/// applied only in an execution, which marks it (`super::implementation_chosen`). The argument
/// is read exactly as the evaluator reads it.
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
        "FLOAT.sign of a NaN reads a sign bit the NaN literal is not given; k-rust's pick, \
         false, applies only in an execution"
            .into()
    })
}

/// Whether `minFloat` or `maxFloat` (`hook`) is applied to `+0.0` and `-0.0`, in either order,
/// of one format the backend computes. Their `smt-hook`s `fp.min` and `fp.max` leave the result
/// on the two zeros unspecified, so the value is one the definition leaves open
/// (`super::chosen_value`, `SignedZero`); the evaluator's `-0.0` for `minFloat` and `+0.0` for
/// `maxFloat` are k-rust's. Two zeros of one sign, and a zero beside a NaN (the other operand),
/// are determined, and two formats are the mixed-format destination ([`mixed_destination`]).
pub(crate) fn signed_zeros(hook: &str, arguments: &[Term]) -> bool {
    if !matches!(hook, "FLOAT.min" | "FLOAT.max") {
        return false;
    }
    let Ok(Some((Operand::Computed(left), Operand::Computed(right)))) =
        read_operands(hook, arguments)
    else {
        return false;
    };
    let zero = |value: KFloat| match value {
        KFloat::Binary32(value) => value == 0.0,
        KFloat::Binary64(value) => value == 0.0,
    };
    left.format() == right.format()
        && zero(left)
        && zero(right)
        && left.is_sign_negative() != right.is_sign_negative()
}

/// Whether `Int2Float`, `roundFloat` or `Float2Int` (`hook`) applied to `arguments`, read as
/// the evaluator reads them, has a value the definition leaves open (class `float-rounding`,
/// `super::chosen_value`); `false` for every other hook.
///
/// "You can convert an integer to a floating-point number with the specified precision and
/// exponent range" (`domains.md`, "Conversion between integer and float") and "Round a
/// floating-point number to a specified precision and exponent range" ("Floating-point
/// mathematics") name no rounding and have no `smt-hook`, so where the argument is not a value
/// of the destination format every neighbour of it there is a model's value: `Int2Float` of an
/// integer the format does not hold, an overflow included, and `roundFloat` of a value the
/// destination does not hold. Where the format holds the argument, the conversion is that
/// element and every model agrees, with one exception: the integer 0 is held by the two zeros,
/// and the text gives no sign, so `Int2Float(0, P, E)` is open too. A `Float` argument is an
/// element of its format, a zero with its sign and the one NaN of a format included, so
/// `roundFloat` of a value the destination holds, `-0.0` and `NaN` among them, is that element.
/// `Float2Int` "rounds to the nearest integer", which decides every argument but a tie, a value
/// exactly halfway between two integers; NaN and the infinities have no nearest integer, which
/// the evaluator leaves unevaluated on every route.
pub(crate) fn rounds(hook: &str, arguments: &[Term]) -> bool {
    let computed = |argument: &Term| match read_float(hook, argument) {
        Ok(Some(Operand::Computed(value))) => Some(value),
        _ => None,
    };
    match (hook, arguments) {
        ("FLOAT.int2float", [integer, precision, exponent_bits]) => {
            let FormatArguments::Format(format) = read_format(precision, exponent_bits) else {
                return false;
            };
            let Some(integer) = read_int(integer) else {
                return false;
            };
            let held = if format.is_binary32() {
                integer.to_f32().map(f64::from)
            } else if format.is_binary64() {
                integer.to_f64()
            } else {
                return false;
            };
            integer.is_zero() || held.and_then(BigInt::from_f64) != Some(integer)
        }
        ("FLOAT.round", [value, precision, exponent_bits]) => {
            let FormatArguments::Format(format) = read_format(precision, exponent_bits) else {
                return false;
            };
            let Some(value) = computed(value) else {
                return false;
            };
            if !format.is_computed() || value.is_nan() {
                return false;
            }
            value.round_to(&format).as_f64() != value.as_f64()
        }
        ("FLOAT.float2int", [value]) => computed(value).is_some_and(|value| {
            let value = value.as_f64();
            value.is_finite() && (value - value.trunc()).abs() == 0.5
        }),
        _ => false,
    }
}

/// Which value of `rootFloat(F, N)` (`arguments`) the definition leaves open, given the
/// evaluator's value `value`: `None` where it determines it.
///
/// "Compute the Nth integer root `rootFloat` of a float" (`domains.md`, "Floating-point
/// mathematics") has no `smt-hook` and names no rounding. For a positive finite `F` and a
/// positive degree it describes the positive real `N`th root: where a float of `F`'s format is
/// that root exactly, every model gives it; where none is, every neighbour of the root is a
/// model's value (class `float-rounding`; `sqrtFloat` follows by its rule `rootFloat(F, 2)`).
/// Elsewhere (a zero, an infinity, a NaN, a negative `F`, a degree of 0 or below) the
/// description gives no value, so every value, and `\bottom`, is a model's (class
/// `outside-domain`): the evaluator's IEEE `rootn` value is k-rust's pick. A negative `F` with an
/// odd degree is among them: the text does not say that "the Nth integer root" of a negative
/// float is its real root.
pub(crate) fn root_open(arguments: &[Term], value: &Term) -> Option<super::ChosenClass> {
    let [radicand, degree] = arguments else {
        return None;
    };
    let Ok(Some(Operand::Computed(radicand))) = read_float("FLOAT.root", radicand) else {
        return None;
    };
    let degree = read_int(degree)?;
    let radicand = radicand.as_f64();
    if !(radicand.is_finite() && radicand > 0.0 && degree.is_positive()) {
        return Some(super::ChosenClass::OutsideDomain);
    }
    let Ok(Some(Operand::Computed(root))) = read_float("FLOAT.root", value) else {
        return None;
    };
    let root = root.as_f64();
    (!(root.is_finite() && root > 0.0 && is_exact_power(root, &degree, radicand)))
        .then_some(super::ChosenClass::FloatRounding)
}

/// Whether `base^degree` is exactly `target`, for positive finite floats and a positive degree.
/// With `base = m * 2^e` and `target = M * 2^E`, `m` and `M` odd, `base^degree` is
/// `m^degree * 2^(e * degree)`, whose odd part is `m^degree`: equal exactly when `m^degree = M`
/// and `e * degree = E`. `M` is below `2^53`, so an odd `m` above 1 fits only a degree below 34.
fn is_exact_power(base: f64, degree: &BigInt, target: f64) -> bool {
    let odd_part = |value: f64| {
        let bits = value.to_bits();
        let field = i64::try_from(bits >> 52).expect("a positive float's 11-bit exponent field");
        let fraction = bits & ((1 << 52) - 1);
        let (mantissa, exponent) = if field == 0 {
            (fraction, -1074)
        } else {
            (fraction | (1 << 52), field - 1075)
        };
        let zeros = mantissa.trailing_zeros();
        (mantissa >> zeros, exponent + i64::from(zeros))
    };
    let ((odd, exponent), (target_odd, target_exponent)) = (odd_part(base), odd_part(target));
    if BigInt::from(exponent) * degree != BigInt::from(target_exponent) {
        return false;
    }
    if odd == 1 {
        return target_odd == 1;
    }
    degree
        .to_u32()
        .filter(|degree| *degree < 64)
        .is_some_and(|degree| BigUint::from(odd).pow(degree) == BigUint::from(target_odd))
}

/// Whether `floorFloat`, `ceilFloat` or `truncFloat` (`hook`) applied to `arguments` has a value
/// the definition leaves open (class `outside-domain`, `super::chosen_value`); `false` for every
/// other hook.
///
/// Each rounds "to the next lowest" (highest; closest in the direction of zero) "floating-point
/// value which is an integer" (`domains.md`, "Floating-point mathematics"). No such value is
/// next to a NaN or an infinity, so the description gives none there (the hooks are `total`: a
/// value exists, which the text does not name). A finite argument that is an integer is that
/// value itself, a zero with its sign included: rounding leaves a value already in the target
/// set. A finite non-integer whose rounding is 0 has two such values, `+0.0` and `-0.0`, equally
/// "an integer" and equally near it, so the sign of the result is open; every other finite
/// argument has exactly one.
pub(crate) fn integral_open(hook: &str, arguments: &[Term]) -> bool {
    if !matches!(hook, "FLOAT.floor" | "FLOAT.ceil" | "FLOAT.trunc") {
        return false;
    }
    let [argument] = arguments else {
        return false;
    };
    let Ok(Some(Operand::Computed(value))) = read_float(hook, argument) else {
        return false;
    };
    let rounded = match hook {
        "FLOAT.floor" => value.floor(),
        "FLOAT.ceil" => value.ceil(),
        _ => value.trunc(),
    }
    .as_f64();
    let value = value.as_f64();
    !value.is_finite() || (rounded == 0.0 && value != 0.0)
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
    /// contains the other, binary64 ([`MixedPair`]). The second is k-rust's pick, which the
    /// root evaluation outside an execution withholds (`super::implementation_chosen`); under a
    /// `choice_sampling` seed the destination is the one the seed chooses, binary32 or binary64,
    /// either of which a model of the definition may take (class `float-destination`).
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
                if let Some(seed) = choice_sampling::seed() {
                    choice_sampling::taken(super::ChosenClass::FloatDestination);
                    if choice_sampling::bit(seed) {
                        return Self::Binary32(destination::binary32_destination(
                            operation, left, right,
                        ));
                    }
                }
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

    /// The adjacent value of the format above (`up`) or below this one: the other rounding
    /// neighbour of a value this one rounds, for the test-only chooser (`crate::choice_sampling`).
    /// The neighbour of the largest finite value is the infinity of its sign, and of an infinity
    /// the largest finite value of its sign; next to a zero lies the least subnormal.
    fn adjacent(self, up: bool) -> Self {
        match (self, up) {
            (Self::Binary32(value), true) => Self::Binary32(value.next_up()),
            (Self::Binary32(value), false) => Self::Binary32(value.next_down()),
            (Self::Binary64(value), true) => Self::Binary64(value.next_up()),
            (Self::Binary64(value), false) => Self::Binary64(value.next_down()),
        }
    }

    /// `+0.0` of this value's format.
    fn positive_zero(self) -> Self {
        match self {
            Self::Binary32(_) => Self::Binary32(0.0),
            Self::Binary64(_) => Self::Binary64(0.0),
        }
    }

    /// The NaN of this value's format.
    fn nan(self) -> Self {
        match self {
            Self::Binary32(_) => Self::Binary32(f32::NAN),
            Self::Binary64(_) => Self::Binary64(f64::NAN),
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
        // Under a `choice_sampling` seed, a NaN's sign bit, which the definition leaves open
        // (`nan_sign`), is the one the seed chooses.
        "FLOAT.sign" => from_token(
            hook,
            arguments,
            |value| {
                if let Some(seed) = choice_sampling::seed()
                    && value.is_nan()
                {
                    choice_sampling::taken(super::ChosenClass::NanSign);
                    bool_term(choice_sampling::bit(seed))
                } else {
                    bool_term(value.is_sign_negative())
                }
            },
            |body, _| {
                if let Some(seed) = choice_sampling::seed()
                    && body == "NaN"
                {
                    choice_sampling::taken(super::ChosenClass::NanSign);
                    bool_term(choice_sampling::bit(seed))
                } else {
                    bool_term(body.starts_with('-'))
                }
            },
        ),
        "FLOAT.isNaN" => from_token(
            hook,
            arguments,
            |value| bool_term(value.is_nan()),
            |body, _| bool_term(body == "NaN"),
        ),
        "FLOAT.neg" => inspect(hook, arguments, |value| float_term(value.neg())),
        "FLOAT.abs" => inspect(hook, arguments, |value| float_term(value.abs())),
        "FLOAT.floor" => inspect(hook, arguments, |value| integral(value, KFloat::floor)),
        "FLOAT.ceil" => inspect(hook, arguments, |value| integral(value, KFloat::ceil)),
        "FLOAT.trunc" => inspect(hook, arguments, |value| integral(value, KFloat::trunc)),
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

/// `floorFloat`, `ceilFloat` or `truncFloat` (`round`) of `value`. Under a `choice_sampling`
/// seed, where the description gives no value ([`integral_open`]) the result is the one the seed
/// chooses (class `outside-domain`): k-rust's, or another value of the format, the other zero
/// for a zero result of a nonzero argument and `+0.0` for a NaN or an infinity.
fn integral(value: KFloat, round: impl FnOnce(KFloat) -> KFloat) -> Term {
    let rounded = round(value);
    if let Some(seed) = choice_sampling::seed() {
        let infinite = !value.as_f64().is_finite();
        let zero_of_nonzero = rounded.as_f64() == 0.0 && value.as_f64() != 0.0;
        if infinite || zero_of_nonzero {
            choice_sampling::taken(super::ChosenClass::OutsideDomain);
            if choice_sampling::bit(seed) {
                return float_term(if infinite {
                    value.positive_zero()
                } else {
                    rounded.neg()
                });
            }
        }
    }
    float_term(rounded)
}

/// `rootFloat(F, N)` ([`KFloat::root`]). Under a `choice_sampling` seed, the value the seed
/// chooses where the text leaves it open ([`root_open`]): for an inexact root of a positive
/// finite `F` in a positive degree the other rounding neighbour of the real root (class
/// `float-rounding`), and outside that domain another value of the format, `+0.0` for k-rust's
/// NaN and NaN otherwise (class `outside-domain`).
fn sampled_root(value: KFloat, degree: &BigInt) -> KFloat {
    let root = value.root(degree);
    let Some(seed) = choice_sampling::seed() else {
        return root;
    };
    let radicand = value.as_f64();
    if !(radicand.is_finite() && radicand > 0.0 && degree.is_positive()) {
        choice_sampling::taken(super::ChosenClass::OutsideDomain);
        if !choice_sampling::bit(seed) {
            return root;
        }
        return if root.is_nan() {
            root.positive_zero()
        } else {
            root.nan()
        };
    }
    if is_exact_power(root.as_f64(), degree, radicand) {
        return root;
    }
    choice_sampling::taken(super::ChosenClass::FloatRounding);
    if !choice_sampling::bit(seed) {
        return root;
    }
    let (format, bits, root_bits) = match (value, root) {
        (KFloat::Binary32(value), KFloat::Binary32(root)) => (
            root::BINARY32,
            u64::from(value.to_bits()),
            u64::from(root.to_bits()),
        ),
        (KFloat::Binary64(value), KFloat::Binary64(root)) => {
            (root::BINARY64, value.to_bits(), root.to_bits())
        }
        _ => unreachable!("a root has its radicand's format"),
    };
    root.adjacent(root::root_exceeds(format, bits, degree, root_bits))
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
    Ok(BuiltinResult::Value(float_term(sampled_root(
        value, &degree,
    ))))
}

/// `roundFloat(F, P, E)`. The format arguments are read first: where they name no format the
/// application is undefined whatever `F` is.
fn round(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 3)?;
    let format = match read_format(&arguments[1], &arguments[2]) {
        FormatArguments::NoFormat => return Ok(BuiltinResult::Bottom(Undefinedness::Stated)),
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
    let rounded = value.round_to(&format);
    // Under a `choice_sampling` seed, a value the destination does not hold rounds to the
    // neighbour the seed chooses (class `float-rounding`): k-rust's nearest, or the other.
    if let Some(seed) = choice_sampling::seed()
        && !value.is_nan()
        && rounded.as_f64() != value.as_f64()
    {
        choice_sampling::taken(super::ChosenClass::FloatRounding);
        if choice_sampling::bit(seed) {
            let above = rounded.as_f64() > value.as_f64();
            return Ok(BuiltinResult::Value(float_term(rounded.adjacent(!above))));
        }
    }
    Ok(BuiltinResult::Value(float_term(rounded)))
}

/// `Int2Float(I, P, E)`. The format arguments are read first: where they name no format the
/// application is undefined whatever `I` is.
fn int_to_float(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 3)?;
    let format = match read_format(&arguments[1], &arguments[2]) {
        FormatArguments::NoFormat => return Ok(BuiltinResult::Bottom(Undefinedness::Stated)),
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
    // Under a `choice_sampling` seed, an integer the format does not hold converts to the
    // neighbour the seed chooses (class `float-rounding`): k-rust's nearest, or the other, an
    // infinity's neighbour being the largest finite value; 0, which both zeros hold, to either.
    if let Some(seed) = choice_sampling::seed() {
        let held = BigInt::from_f64(value.as_f64());
        if integer.is_zero() || held.as_ref() != Some(&integer) {
            choice_sampling::taken(super::ChosenClass::FloatRounding);
            if choice_sampling::bit(seed) {
                let other = match held {
                    _ if integer.is_zero() => value.neg(),
                    Some(held) => value.adjacent(held < integer),
                    None => value.adjacent(value.is_sign_negative()),
                };
                return Ok(BuiltinResult::Value(float_term(other)));
            }
        }
    }
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
            // Under a `choice_sampling` seed, a tie rounds to the integer the seed chooses
            // (class `float-rounding`): k-rust's even one, or the other.
            let exact = value.as_f64();
            if let Some(seed) = choice_sampling::seed()
                && (exact - exact.trunc()).abs() == 0.5
            {
                choice_sampling::taken(super::ChosenClass::FloatRounding);
                if choice_sampling::bit(seed) {
                    // A tie is below 2^52 in magnitude, so its nearest integers are exact.
                    let above = integer.to_f64().is_some_and(|rounded| rounded > exact);
                    return BuiltinResult::Value(int_term(if above {
                        integer - 1
                    } else {
                        integer + 1
                    }));
                }
            }
            BuiltinResult::Value(int_term(integer))
        }))
}

fn maximum_value(hook: &str, arguments: &[Term]) -> HookResult<BuiltinResult> {
    expect_arity(hook, arguments, 2)?;
    let format = match read_format(&arguments[0], &arguments[1]) {
        FormatArguments::NoFormat => return Ok(BuiltinResult::Bottom(Undefinedness::Stated)),
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

fn invalid_token(hook: &str, token: &str) -> BuiltinError {
    BuiltinError::InvalidFloatToken {
        hook: hook.into(),
        token: token.into(),
    }
}

fn minimum_f32(left: f32, right: f32) -> f32 {
    if left.is_nan() {
        right
    } else if right.is_nan() || left < right {
        left
    } else if right < left {
        right
    } else if left == 0.0 && (left.is_sign_negative() || right.is_sign_negative()) {
        if let Some(seed) = choice_sampling::seed()
            && left.is_sign_negative() != right.is_sign_negative()
        {
            choice_sampling::taken(super::ChosenClass::SignedZero);
            if choice_sampling::bit(seed) {
                0.0
            } else {
                -0.0
            }
        } else {
            -0.0
        }
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
        if let Some(seed) = choice_sampling::seed()
            && left.is_sign_negative() != right.is_sign_negative()
        {
            choice_sampling::taken(super::ChosenClass::SignedZero);
            if choice_sampling::bit(seed) {
                -0.0
            } else {
                0.0
            }
        } else {
            0.0
        }
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
        if let Some(seed) = choice_sampling::seed()
            && left.is_sign_negative() != right.is_sign_negative()
        {
            choice_sampling::taken(super::ChosenClass::SignedZero);
            if choice_sampling::bit(seed) {
                0.0
            } else {
                -0.0
            }
        } else {
            -0.0
        }
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
        if let Some(seed) = choice_sampling::seed()
            && left.is_sign_negative() != right.is_sign_negative()
        {
            choice_sampling::taken(super::ChosenClass::SignedZero);
            if choice_sampling::bit(seed) {
                -0.0
            } else {
                0.0
            }
        } else {
            0.0
        }
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

    /// Under a `choice_sampling` seed whose bit is set, every `float-rounding` site gives the
    /// other rounding neighbour, adjacent to k-rust's value and on the other side of the exact
    /// result, and every `outside-domain` site another value of the format: each is a value some
    /// model of the text gives.
    #[cfg(feature = "choice-sampling")]
    #[test]
    fn a_seed_takes_the_other_rounding_neighbour_and_another_value_outside_the_domain() {
        use std::num::NonZeroU64;
        let value = |hook: &str, arguments: &[Term]| match evaluate(hook, arguments) {
            Ok(BuiltinResult::Value(value)) => value,
            other => panic!("{hook} has a value: {other:?}"),
        };
        let number = |term: &Term| match read_float("test", term) {
            Ok(Some(Operand::Computed(value))) => value,
            _ => panic!("a computed Float: {term:?}"),
        };
        let int = |value: i64| int_term(BigInt::from(value));
        let both = |hook: &str, arguments: &[Term]| {
            let own = value(hook, arguments);
            let other = crate::choice_sampling::with_seed(NonZeroU64::new(1).unwrap(), || {
                value(hook, arguments)
            });
            (own, other)
        };
        let floats = |hook: &str, arguments: &[Term]| {
            let (own, other) = both(hook, arguments);
            (number(&own), number(&other))
        };
        // 2^24 + 1 lies between 2^24 and 2^24 + 2; k-rust takes the even one.
        let (own, other) = floats("FLOAT.int2float", &[int(16_777_217), int(24), int(8)]);
        assert_eq!((own.as_f64(), other.as_f64()), (16_777_216.0, 16_777_218.0));
        // 0 is held by both zeros.
        let (own, other) = floats("FLOAT.int2float", &[int(0), int(24), int(8)]);
        assert!(!own.is_sign_negative() && other.is_sign_negative() && other.as_f64() == 0.0);
        // Past the largest finite binary32 value by more than half an ulp: infinity and the
        // largest finite value.
        let big = BigInt::from(2).pow(128u32);
        let (own, other) = floats("FLOAT.int2float", &[int_term(big.clone()), int(24), int(8)]);
        assert_eq!(
            (own.as_f64(), other.as_f64()),
            (f64::INFINITY, f64::from(f32::MAX))
        );
        let (own, other) = floats("FLOAT.int2float", &[int_term(-big), int(24), int(8)]);
        assert_eq!(
            (own.as_f64(), other.as_f64()),
            (f64::NEG_INFINITY, -f64::from(f32::MAX))
        );
        // roundFloat: the binary32 neighbours of binary64 0.1, and of a value below the least
        // subnormal, whose neighbours are a zero and the least subnormal.
        for (token, source) in [
            ("0.1", 0.1_f64),
            ("1.0e-50", 1.0e-50),
            ("-1.0e-50", -1.0e-50),
            ("1.0e300", 1.0e300),
        ] {
            let (own, other) = floats("FLOAT.round", &[float(token), int(24), int(8)]);
            let (KFloat::Binary32(own), KFloat::Binary32(other)) = (own, other) else {
                panic!("binary32 results");
            };
            assert!(
                other == own.next_up() || other == own.next_down(),
                "{source}: {own} and {other} are adjacent"
            );
            assert!(
                (f64::from(own) - source).signum() != (f64::from(other) - source).signum(),
                "{source}: {own} and {other} enclose it"
            );
        }
        // Float2Int at a tie: the other integer.
        for (tie, own, other) in [("2.5", 2, 3), ("-2.5", -2, -3), ("3.5", 4, 3)] {
            assert_eq!(
                both("FLOAT.float2int", &[float(tie)]),
                (int(own), int(other)),
                "{tie}"
            );
        }
        // An inexact root, native (2) and computed (3) degrees, both formats: the neighbours
        // enclose the real root.
        for (radicand, degree, real) in [
            ("2.0f", 3, 2.0_f64.cbrt()),
            ("2.0f", 2, 2.0_f64.sqrt()),
            ("3.0f", 3, 3.0_f64.cbrt()),
            ("0.5f", 5, 0.5_f64.powf(0.2)),
        ] {
            let (own, other) = floats("FLOAT.root", &[float(radicand), int(degree)]);
            assert!(
                other.as_f64() == own.adjacent(true).as_f64()
                    || other.as_f64() == own.adjacent(false).as_f64(),
                "rootFloat({radicand}, {degree}): {own:?} and {other:?} are adjacent"
            );
            assert!(
                (own.as_f64() - real).signum() != (other.as_f64() - real).signum(),
                "rootFloat({radicand}, {degree}): {own:?} and {other:?} enclose {real}"
            );
        }
        // binary64, decided exactly: the cubes of the two neighbours enclose 3.
        let cube_exceeds_three = |root: KFloat| {
            let bits = root.as_f64().to_bits();
            let exponent = i64::try_from(bits >> 52).unwrap() - 1075;
            let significand = BigInt::from((bits & ((1 << 52) - 1)) | (1 << 52));
            let shift = usize::try_from(-3 * exponent).unwrap();
            significand.pow(3) > (BigInt::from(3) << shift)
        };
        let (own, other) = floats("FLOAT.root", &[float("3.0"), int(3)]);
        assert!(
            other.as_f64() == own.adjacent(true).as_f64()
                || other.as_f64() == own.adjacent(false).as_f64()
        );
        assert_ne!(cube_exceeds_three(own), cube_exceeds_three(other));
        // Outside the domain: another value of the format.
        let (own, other) = floats("FLOAT.root", &[float("-4.0"), int(2)]);
        assert!(own.is_nan() && other.as_f64() == 0.0);
        let (own, other) = floats("FLOAT.root", &[float("0.0"), int(3)]);
        assert!(own.as_f64() == 0.0 && other.is_nan());
        let (own, other) = floats("FLOAT.floor", &[float("0.5")]);
        assert!(own.as_f64() == 0.0 && !own.is_sign_negative());
        assert!(other.as_f64() == 0.0 && other.is_sign_negative());
        let (own, other) = floats("FLOAT.ceil", &[float("Infinity")]);
        assert!(own.as_f64() == f64::INFINITY && other.as_f64() == 0.0);
        // Determined values do not move.
        for (hook, arguments) in [
            ("FLOAT.int2float", vec![int(3), int(24), int(8)]),
            ("FLOAT.round", vec![float("0.5"), int(24), int(8)]),
            ("FLOAT.float2int", vec![float("2.4")]),
            ("FLOAT.root", vec![float("4.0"), int(2)]),
            ("FLOAT.floor", vec![float("1.5")]),
        ] {
            let (own, other) = both(hook, &arguments);
            assert_eq!(own, other, "{hook}");
        }
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
