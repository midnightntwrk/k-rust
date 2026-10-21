//! The long form of `krs-patterns-functions-sugar`: the structs and
//! `#[k::equation]` fns its function shorthand and equation tables stand for,
//! with the default templates written out. Both emit the same K, byte for
//! byte.

use k::builtin::KSequence;
use k::builtin::bool::Bool;
use k::builtin::int::{self, Int};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    Reg: Value;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((ByteOf, HalfOf, RegOf, PickOf))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("byteOf({value})")]
    ByteOf { value: Int },
    #[k::syntax("halfOf({value})")]
    HalfOf { value: Int },
    #[k::syntax("regOf({index})")]
    RegOf { index: Int },
    #[k::syntax("pickOf({flag}, {value})")]
    PickOf { flag: Bool, value: Int },
}

#[k::constructors(sort = Reg, result = KResult)]
#[k::precedence((A, B, Hl))]
#[rustfmt::skip]
pub enum Register {
    #[k::syntax("ra")]
    A,
    #[k::syntax("rb")]
    B,
    #[k::syntax("rhl")]
    Hl,
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

/// The low 8 bits of an integer.
#[k::function(total, internal, sort = Int, syntax = "byte({value})")]
pub struct Byte {
    pub value: Term<Int>,
}

#[k::equation]
fn byte(k::term![Byte(value)]: Term<Int>) -> Term<Int> {
    int::rem_euclid(value, 256)
}

/// Half of a natural number.
#[k::function(partial, sort = Int, syntax = "half({value})")]
#[allow(dead_code)]
struct Half {
    value: Term<Int>,
}

#[k::requires(int::ge(value, 0))]
#[k::equation]
fn half(k::term![Half(value)]: Term<Int>) -> Term<Int> {
    int::div(value, 2)
}

/// The register an index names.
#[k::function(total, internal, sort = Reg, syntax = "r8({index})")]
pub struct R8 {
    pub index: Term<Int>,
}

#[k::equation]
fn r8_a(k::term![R8(0)]: Term<Reg>) -> Term<Reg> {
    Register::A
}

#[k::equation]
fn r8_b(k::term![R8(1)]: Term<Reg>) -> Term<Reg> {
    Register::B
}

/// The register pair.
#[k::equation]
fn r8_hl(k::term![R8(-1)]: Term<Reg>) -> Term<Reg> {
    Register::Hl
}

#[k::equation(owise)]
fn r8_other(k::term![R8(_)]: Term<Reg>) -> Term<Reg> {
    Register::A
}

/// `value` when `flag` holds, `0` otherwise.
#[k::function(total, internal, sort = Int, syntax = "pick({flag}, {value})")]
pub struct Pick {
    pub flag: Term<Bool>,
    pub value: Term<Int>,
}

#[k::equation]
fn pick_true(k::term![Pick(true, v)]: Term<Int>) -> Term<Int> {
    v
}

#[k::equation]
fn pick_false(k::term![Pick(false, _)]: Term<Int>) -> Term<Int> {
    0
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    byte_of: ByteOf(v)    => crate::Byte(v);
    half_of: HalfOf(v)    => crate::Half(v);
    reg_of : RegOf(i)     => crate::R8(i);
    pick_of: PickOf(f, v) => crate::Pick(f, v);
}
