//! HALT (`01 110 110`, the literal `118`) and `LD r, r'` (`01 yyy zzz`),
//! written as `#[k::equation]` fns as SM83 writes its decoder, where `LD`
//! forgets `op != 118`: both define `Decode(118)` at one priority with
//! different results.

use k::Term;
use k::builtin::KSequence;
use k::builtin::int::Int;

k::sorts! {
    Instr;
}

#[k::constructors(sort = Instr, result = k::KResult)]
#[k::precedence((Halt, Ld))]
#[rustfmt::skip]
pub enum Instruction {
    #[k::syntax("halt")]
    Halt,
    #[k::syntax("ld {dst} {src}")]
    Ld { dst: Int, src: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![] }
    }
}

/// The instruction an opcode encodes.
#[k::function(total, internal)]
pub fn Decode(opcode: Term<Int>) -> Term<Instr>;

#[k::equation]
fn decode_halt(k::term![Decode(118)]: Term<Instr>) -> Term<Instr> {
    Instruction::Halt()
}

#[k::equation]
fn decode_ld_r_r(k::term![Decode(k::bits!("01 yyy zzz"))]: Term<Instr>) -> Term<Instr> {
    Instruction::Ld(y, z)
}

#[k::equation(owise)]
fn decode_other(k::term![Decode(_)]: Term<Instr>) -> Term<Instr> {
    Instruction::Halt()
}
