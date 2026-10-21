//! Function shorthand and equation tables.
//!
//! The definition is pure sugar: `krs-patterns-functions-sugar-long` writes
//! the structs and `#[k::equation]` fns it stands for, and both emit the same
//! K, byte for byte.
//!
//! - `byteOf(300)` is `44`: `Byte` is a function declared by a `fn` whose body
//!   is its one equation, `byte(value) = value modInt 256`, with the default
//!   syntax `byte({value})` of an `internal` function;
//! - `halfOf(9)` is `4`: `Half` is a private function whose equation is
//!   guarded by the `#[k::requires]` above it;
//! - `regOf(1)` is `rb`, `regOf(-1)` is `rhl`, and `regOf(9)` is `ra`: `R8` is
//!   declared by a `fn` without a body and defined by a table whose rows name
//!   registers through the table's `use` items, with an `owise` row;
//! - `pickOf(true, 7)` is `7` and `pickOf(false, 7)` is `0`: `Pick` is a
//!   struct whose default syntax is `pick({flag}, {value})`, defined by a table
//!   of two-argument rows.

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
#[k::function(total, internal)]
pub fn Byte(value: Term<Int>) -> Term<Int> {
    int::rem_euclid(value, 256)
}

/// Half of a natural number.
#[k::requires(int::ge(value, 0))]
#[k::function(partial)]
fn Half(value: Term<Int>) -> Term<Int> {
    int::div(value, 2)
}

/// The register an index names.
#[k::function(total, internal)]
pub fn R8(index: Term<Int>) -> Term<Reg>;

k::equations! {
    for R8;
    use Register::*;
    r8_a    : 0  => A;
    r8_b    : 1  => B;
    /// The register pair.
    r8_hl   : -1 => Hl;
    #[k::equation(owise)]
    r8_other: _  => A;
}

/// `value` when `flag` holds, `0` otherwise.
#[k::function(total, internal, sort = Int)]
pub struct Pick {
    pub flag: Term<Bool>,
    pub value: Term<Int>,
}

k::equations! {
    for Pick;
    pick_true : (true, v)  => v;
    pick_false: (false, _) => 0;
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    byte_of: ByteOf(v)    => crate::Byte(v);
    half_of: HalfOf(v)    => crate::Half(v);
    reg_of : RegOf(i)     => crate::R8(i);
    pick_of: PickOf(f, v) => crate::Pick(f, v);
}
