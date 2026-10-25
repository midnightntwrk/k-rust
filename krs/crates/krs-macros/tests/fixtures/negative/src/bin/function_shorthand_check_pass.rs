//@ check-pass
//! The function shorthand, a bodiless declaration, a default syntax on a
//! struct, and an equation table with several `use` items compile, including
//! qualified paths through a renamed import.
use renamed_krs as k;
use renamed_krs::builtin::{Bool, Int, int};

renamed_krs::sorts! {
    Reg8;
    Operand8;
}

#[k::constructors(sort = Reg8, result = renamed_krs::KResult)]
#[k::precedence((A, B))]
pub enum Register {
    #[k::syntax("ra")]
    A,
    #[k::syntax("rb")]
    B,
}

#[k::constructors(sort = Operand8, result = renamed_krs::KResult)]
#[k::precedence((Reg, Indirect))]
pub enum Operand {
    #[k::syntax("reg({r})")]
    Reg { r: Reg8 },
    #[k::syntax("(hl)")]
    Indirect,
}

/// The low 8 bits.
#[k::function(total, internal)]
pub fn Byte(value: k::Term<Int>) -> k::Term<Int> {
    int::rem_euclid(value, 256)
}

#[k::requires(int::ge(value, 0))]
#[k::function(partial)]
fn Half(value: k::Term<Int>) -> k::Term<Int> {
    int::div(value, 2)
}

#[k::function(total, internal)]
pub fn R8(index: k::Term<Int>) -> k::Term<Operand8>;

k::equations! {
    for R8;
    use Operand::*;
    use Register::*;
    r8_a: 0 => Reg(A);
    r8_b: -1 => Reg(B);
    #[k::equation(owise)]
    r8_other: _ => Indirect;
}

/// A table keyed on unit variants: `A()` and `Register::B` name them.
#[k::function(total, internal)]
pub fn Index(register: k::Term<Reg8>) -> k::Term<Int>;

k::equations! {
    for Index;
    use Register::*;
    index_a: A() => 0;
    index_b: Register::B => 1;
}

/// A renamed import qualifies a row's paths: `Reg::B` is `Register::B`, in a
/// pattern and in a result.
#[k::function(total, internal)]
pub fn Swap(register: k::Term<Reg8>) -> k::Term<Reg8>;

k::equations! {
    for Swap;
    use Register as Reg;
    swap_a: Reg::A => Reg::B;
    swap_b: Reg::B => Reg::A;
}

#[k::function(total, internal, sort = Int)]
pub struct Pick {
    pub flag: k::Term<Bool>,
    pub value: k::Term<Int>,
}

k::equations! {
    for Pick;
    pick_true: (true, v) => int::add(Byte(v), Half(v));
    pick_false: (false, _) => 0;
}

fn main() {}
