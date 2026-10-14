//! Builtin INT operations: one function and one equation per operation.
//!
//! Each program applies one function to concrete arguments; the native route
//! and Java K's LLVM backend must evaluate it to the same value.

use k::builtin::{Bool, Int, KSequence, int};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
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

/// `int::add`, `+Int`.
#[k::function(total, sort = Int, syntax = "add({a}, {b})")]
pub struct Add {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn add(k::term![Add(a, b)]: Term<Int>) -> Term<Int> {
    int::add(a, b)
}

/// `int::sub`, `-Int`.
#[k::function(total, sort = Int, syntax = "sub({a}, {b})")]
pub struct Sub {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn sub(k::term![Sub(a, b)]: Term<Int>) -> Term<Int> {
    int::sub(a, b)
}

/// `int::mul`, `*Int`.
#[k::function(total, sort = Int, syntax = "mul({a}, {b})")]
pub struct Mul {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn mul(k::term![Mul(a, b)]: Term<Int>) -> Term<Int> {
    int::mul(a, b)
}

/// `int::div`, `/Int`, truncating like Rust's `/`.
#[k::function(total, sort = Int, syntax = "div({a}, {b})")]
pub struct Div {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn div(k::term![Div(a, b)]: Term<Int>) -> Term<Int> {
    int::div(a, b)
}

/// `int::rem`, `%Int`, truncating like Rust's `%`.
#[k::function(total, sort = Int, syntax = "rem({a}, {b})")]
pub struct Rem {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn rem(k::term![Rem(a, b)]: Term<Int>) -> Term<Int> {
    int::rem(a, b)
}

/// `int::div_euclid`, `divInt`, like `i64::div_euclid`.
#[k::function(total, sort = Int, syntax = "divEuclid({a}, {b})")]
pub struct DivEuclid {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn div_euclid(k::term![DivEuclid(a, b)]: Term<Int>) -> Term<Int> {
    int::div_euclid(a, b)
}

/// `int::rem_euclid`, `modInt`, like `i64::rem_euclid`.
#[k::function(total, sort = Int, syntax = "remEuclid({a}, {b})")]
pub struct RemEuclid {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn rem_euclid(k::term![RemEuclid(a, b)]: Term<Int>) -> Term<Int> {
    int::rem_euclid(a, b)
}

/// `int::pow`, `^Int`.
#[k::function(total, sort = Int, syntax = "pow({a}, {b})")]
pub struct Pow {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn pow(k::term![Pow(a, b)]: Term<Int>) -> Term<Int> {
    int::pow(a, b)
}

/// `int::pow_mod`, `^%Int`.
#[k::function(total, sort = Int, syntax = "powMod({a}, {b}, {c})")]
pub struct PowMod {
    pub a: Term<Int>,
    pub b: Term<Int>,
    pub c: Term<Int>,
}

#[k::equation]
fn pow_mod(k::term![PowMod(a, b, c)]: Term<Int>) -> Term<Int> {
    int::pow_mod(a, b, c)
}

/// `int::shift_left`, `<<Int`.
#[k::function(total, sort = Int, syntax = "shl({a}, {b})")]
pub struct ShiftLeft {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn shift_left(k::term![ShiftLeft(a, b)]: Term<Int>) -> Term<Int> {
    int::shift_left(a, b)
}

/// `int::shift_right`, `>>Int`.
#[k::function(total, sort = Int, syntax = "shr({a}, {b})")]
pub struct ShiftRight {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn shift_right(k::term![ShiftRight(a, b)]: Term<Int>) -> Term<Int> {
    int::shift_right(a, b)
}

/// `int::bit_and`, `&Int`.
#[k::function(total, sort = Int, syntax = "bitAnd({a}, {b})")]
pub struct BitAnd {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn bit_and(k::term![BitAnd(a, b)]: Term<Int>) -> Term<Int> {
    int::bit_and(a, b)
}

/// `int::bit_or`, `|Int`.
#[k::function(total, sort = Int, syntax = "bitOr({a}, {b})")]
pub struct BitOr {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn bit_or(k::term![BitOr(a, b)]: Term<Int>) -> Term<Int> {
    int::bit_or(a, b)
}

/// `int::bit_xor`, `xorInt`.
#[k::function(total, sort = Int, syntax = "bitXor({a}, {b})")]
pub struct BitXor {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn bit_xor(k::term![BitXor(a, b)]: Term<Int>) -> Term<Int> {
    int::bit_xor(a, b)
}

/// `int::bit_not`, `~Int`.
#[k::function(total, sort = Int, syntax = "bitNot({a})")]
pub struct BitNot {
    pub a: Term<Int>,
}

#[k::equation]
fn bit_not(k::term![BitNot(a)]: Term<Int>) -> Term<Int> {
    int::bit_not(a)
}

/// `int::min`, `minInt`.
#[k::function(total, sort = Int, syntax = "min({a}, {b})")]
pub struct Min {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn min(k::term![Min(a, b)]: Term<Int>) -> Term<Int> {
    int::min(a, b)
}

/// `int::max`, `maxInt`.
#[k::function(total, sort = Int, syntax = "max({a}, {b})")]
pub struct Max {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn max(k::term![Max(a, b)]: Term<Int>) -> Term<Int> {
    int::max(a, b)
}

/// `int::abs`, `absInt`.
#[k::function(total, sort = Int, syntax = "abs({a})")]
pub struct Abs {
    pub a: Term<Int>,
}

#[k::equation]
fn abs(k::term![Abs(a)]: Term<Int>) -> Term<Int> {
    int::abs(a)
}

/// `int::log2`, `log2Int`.
#[k::function(total, sort = Int, syntax = "log2({a})")]
pub struct Log2 {
    pub a: Term<Int>,
}

#[k::equation]
fn log2(k::term![Log2(a)]: Term<Int>) -> Term<Int> {
    int::log2(a)
}

/// `int::bit_range`, `bitRangeInt`.
#[k::function(total, sort = Int, syntax = "bitRange({a}, {b}, {c})")]
pub struct BitRange {
    pub a: Term<Int>,
    pub b: Term<Int>,
    pub c: Term<Int>,
}

#[k::equation]
fn bit_range(k::term![BitRange(a, b, c)]: Term<Int>) -> Term<Int> {
    int::bit_range(a, b, c)
}

/// `int::sign_extend_bit_range`, `signExtendBitRangeInt`.
#[k::function(total, sort = Int, syntax = "signExtendBitRange({a}, {b}, {c})")]
pub struct SignExtendBitRange {
    pub a: Term<Int>,
    pub b: Term<Int>,
    pub c: Term<Int>,
}

#[k::equation]
fn sign_extend_bit_range(k::term![SignExtendBitRange(a, b, c)]: Term<Int>) -> Term<Int> {
    int::sign_extend_bit_range(a, b, c)
}

/// `int::divides`, `dividesInt`.
#[k::function(total, sort = Bool, syntax = "divides({a}, {b})")]
pub struct Divides {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn divides(k::term![Divides(a, b)]: Term<Bool>) -> Term<Bool> {
    int::divides(a, b)
}

/// `int::eq`, `==Int`.
#[k::function(total, sort = Bool, syntax = "eq({a}, {b})")]
pub struct Eq {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn eq(k::term![Eq(a, b)]: Term<Bool>) -> Term<Bool> {
    int::eq(a, b)
}

/// `int::ne`, `=/=Int`.
#[k::function(total, sort = Bool, syntax = "ne({a}, {b})")]
pub struct Ne {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn ne(k::term![Ne(a, b)]: Term<Bool>) -> Term<Bool> {
    int::ne(a, b)
}

/// `int::lt`, `<Int`.
#[k::function(total, sort = Bool, syntax = "lt({a}, {b})")]
pub struct Lt {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn lt(k::term![Lt(a, b)]: Term<Bool>) -> Term<Bool> {
    int::lt(a, b)
}

/// `int::le`, `<=Int`.
#[k::function(total, sort = Bool, syntax = "le({a}, {b})")]
pub struct Le {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn le(k::term![Le(a, b)]: Term<Bool>) -> Term<Bool> {
    int::le(a, b)
}

/// `int::gt`, `>Int`.
#[k::function(total, sort = Bool, syntax = "gt({a}, {b})")]
pub struct Gt {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn gt(k::term![Gt(a, b)]: Term<Bool>) -> Term<Bool> {
    int::gt(a, b)
}

/// `int::ge`, `>=Int`.
#[k::function(total, sort = Bool, syntax = "ge({a}, {b})")]
pub struct Ge {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

#[k::equation]
fn ge(k::term![Ge(a, b)]: Term<Bool>) -> Term<Bool> {
    int::ge(a, b)
}
