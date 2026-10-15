//! Float literals and FLOAT operations (KF-033).
//!
//! K has one `Float` sort, and every value carries its precision: a Rust float
//! literal is a K Float token (`0.1f32` is `0.1f`, `1.5` and `1.5f64` are
//! binary64), and `f64::NAN`, `f64::INFINITY`, and `f64::NEG_INFINITY` are `NaN`,
//! `Infinity`, and `-Infinity`. The operations follow IEEE 754 in the operands'
//! format.
//!
//! The native frontend folds a FLOAT-hooked application whose arguments are all
//! tokens, which KRS records as a capability its native routes do not claim yet,
//! so every operation below is applied to a variable and the programs supply
//! the values. `negate` leaves
//! a Float in the computation cell, so both routes print a Float result.

use k::builtin::{Bool, Float, Int, KSequence, bool, float, int, kequal};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Float, Int;
}

/// A constructor matched against Float literals by readable rules.
#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Classify))]
#[rustfmt::skip]
pub enum Classifier {
    #[k::syntax("classify({value})")]
    Classify { value: Float },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::rules! {
    for Exp;
    use Classifier::*;

    one_and_a_half: Classify(1.5)               => 1;
    single_tenth  : Classify(0.1f32)            => 2;
    positive_inf  : Classify(f64::INFINITY)     => 3;
    negative_inf  : Classify(f64::NEG_INFINITY) => 4;
    negative_zero : Classify(-0.0)              => 5;
}

/// IEEE equality of a sum: `float::eq(float::add(a, b), c)`.
#[k::function(total, sort = Bool, syntax = "sumIs({a}, {b}, {c})")]
pub struct SumIs {
    pub a: Term<Float>,
    pub b: Term<Float>,
    pub c: Term<Float>,
}

#[k::equation]
fn sum_is(k::term![SumIs(a, b, c)]: Term<Bool>) -> Term<Bool> {
    float::eq(float::add(a, b), c)
}

/// Each arithmetic operation against an expected value.
#[k::function(total, sort = Bool, syntax = "arithmetic({a}, {b})")]
pub struct Arithmetic {
    pub a: Term<Float>,
    pub b: Term<Float>,
}

#[k::equation]
fn arithmetic(k::term![Arithmetic(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::and(
        bool::and(
            float::eq(float::sub(a, b), 1.25),
            float::eq(float::mul(a, b), 0.375),
        ),
        bool::and(float::eq(float::div(a, b), 6.0), float::lt(b, a)),
    )
}

/// IEEE equality, `==Float`: NaN equals nothing, and `0.0` equals `-0.0`.
#[k::function(total, sort = Bool, syntax = "ieeeEq({a}, {b})")]
pub struct IeeeEq {
    pub a: Term<Float>,
    pub b: Term<Float>,
}

#[k::equation]
fn ieee_eq(k::term![IeeeEq(a, b)]: Term<Bool>) -> Term<Bool> {
    float::eq(a, b)
}

/// `float::ne`, the negation of `==Float`.
#[k::function(total, sort = Bool, syntax = "ieeeNe({a}, {b})")]
pub struct IeeeNe {
    pub a: Term<Float>,
    pub b: Term<Float>,
}

#[k::equation]
fn ieee_ne(k::term![IeeeNe(a, b)]: Term<Bool>) -> Term<Bool> {
    float::ne(a, b)
}

/// Term equality, `==K`, which compares the tokens.
#[k::function(total, sort = Bool, syntax = "termEq({a}, {b})")]
pub struct TermEq {
    pub a: Term<Float>,
    pub b: Term<Float>,
}

#[k::equation]
fn term_eq(k::term![TermEq(a, b)]: Term<Bool>) -> Term<Bool> {
    kequal::eq(a, b)
}

/// `float::is_nan`.
#[k::function(total, sort = Bool, syntax = "nan({a})")]
pub struct IsNan {
    pub a: Term<Float>,
}

#[k::equation]
fn is_nan(k::term![IsNan(a)]: Term<Bool>) -> Term<Bool> {
    float::is_nan(a)
}

/// `float::is_infinite`.
#[k::function(total, sort = Bool, syntax = "infinite({a})")]
pub struct IsInfinite {
    pub a: Term<Float>,
}

#[k::equation]
fn is_infinite(k::term![IsInfinite(a)]: Term<Bool>) -> Term<Bool> {
    float::is_infinite(a)
}

/// The sign bit of the negation: `float::sign(float::neg(a))`.
#[k::function(total, sort = Bool, syntax = "negativeSign({a})")]
pub struct NegativeSign {
    pub a: Term<Float>,
}

#[k::equation]
fn negative_sign(k::term![NegativeSign(a)]: Term<Bool>) -> Term<Bool> {
    float::sign(float::neg(a))
}

/// `float::sqrt` against an expected root.
#[k::function(total, sort = Bool, syntax = "sqrtIs({a}, {root})")]
pub struct SqrtIs {
    pub a: Term<Float>,
    pub root: Term<Float>,
}

#[k::equation]
fn sqrt_is(k::term![SqrtIs(a, root)]: Term<Bool>) -> Term<Bool> {
    bool::and(
        float::eq(float::sqrt(a), root),
        float::eq(float::root(a, 2), root),
    )
}

/// The four roundings to an integral value and `abs`, `min`, `max`.
#[k::function(total, sort = Bool, syntax = "rounding({a})")]
pub struct Rounding {
    pub a: Term<Float>,
}

#[k::equation]
fn rounding(k::term![Rounding(a)]: Term<Bool>) -> Term<Bool> {
    bool::and(
        bool::and(
            float::eq(float::floor(a), -3.0),
            float::eq(float::ceil(a), -2.0),
        ),
        bool::and(
            bool::and(
                float::eq(float::trunc(a), -2.0),
                float::eq(float::abs(a), 2.5),
            ),
            bool::and(
                float::eq(float::min(a, 0.0), a),
                float::eq(float::max(a, 0.0), 0.0),
            ),
        ),
    )
}

/// `float::to_int`, which rounds ties to even.
#[k::function(total, sort = Int, syntax = "toInt({a})")]
pub struct ToInt {
    pub a: Term<Float>,
}

#[k::equation]
fn to_int(k::term![ToInt(a)]: Term<Int>) -> Term<Int> {
    float::to_int(a)
}

/// `float::from_int` in a format, against an expected value.
#[k::function(partial, sort = Bool, syntax = "fromIntIs({i}, {precision}, {exponent}, {expected})")]
pub struct FromIntIs {
    pub i: Term<Int>,
    pub precision: Term<Int>,
    pub exponent: Term<Int>,
    pub expected: Term<Float>,
}

#[k::equation]
fn from_int_is(k::term![FromIntIs(i, precision, exponent, expected)]: Term<Bool>) -> Term<Bool> {
    float::eq(float::from_int(i, precision, exponent), expected)
}

/// `float::round` to a format, against an expected value.
#[k::function(partial, sort = Bool, syntax = "roundIs({a}, {precision}, {exponent}, {expected})")]
pub struct RoundIs {
    pub a: Term<Float>,
    pub precision: Term<Int>,
    pub exponent: Term<Int>,
    pub expected: Term<Float>,
}

#[k::equation]
fn round_is(k::term![RoundIs(a, precision, exponent, expected)]: Term<Bool>) -> Term<Bool> {
    float::eq(float::round(a, precision, exponent), expected)
}

/// `float::max_value` of a format, against an expected value.
#[k::function(partial, sort = Bool, syntax = "maxValueIs({precision}, {exponent}, {expected})")]
pub struct MaxValueIs {
    pub precision: Term<Int>,
    pub exponent: Term<Int>,
    pub expected: Term<Float>,
}

#[k::equation]
fn max_value_is(k::term![MaxValueIs(precision, exponent, expected)]: Term<Bool>) -> Term<Bool> {
    float::eq(float::max_value(precision, exponent), expected)
}

/// The precision and exponent bits of a value's format, as `p * 100 + e`.
#[k::function(total, sort = Int, syntax = "format({a})")]
pub struct Format {
    pub a: Term<Float>,
}

#[k::equation]
fn format(k::term![Format(a)]: Term<Int>) -> Term<Int> {
    int::add(int::mul(float::precision(a), 100), float::exponent_bits(a))
}

/// The orderings, which are false whenever an operand is NaN.
#[k::function(total, sort = Bool, syntax = "ordered({a}, {b})")]
pub struct Ordered {
    pub a: Term<Float>,
    pub b: Term<Float>,
}

#[k::equation]
fn ordered(k::term![Ordered(a, b)]: Term<Bool>) -> Term<Bool> {
    bool::or(
        bool::or(float::lt(a, b), float::le(a, b)),
        bool::or(float::gt(a, b), float::ge(a, b)),
    )
}

/// The negation of a value, in its own format: the program's result is a
/// Float, which both routes print as K's LLVM backend does.
#[k::function(total, sort = Float, syntax = "negate({a})")]
pub struct Negate {
    pub a: Term<Float>,
}

#[k::equation]
fn negate(k::term![Negate(a)]: Term<Float>) -> Term<Float> {
    float::neg(a)
}
