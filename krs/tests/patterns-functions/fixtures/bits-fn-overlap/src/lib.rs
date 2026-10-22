//! An `#[k::equation]` fn whose template (`1_ yyy ___`) meets a table row's
//! (`10 1__ bbb`) at one priority: both define `Decode(160)`.

use k::Term;
use k::builtin::KSequence;
use k::builtin::int::Int;

k::sorts! {
    Instr;
}

#[k::constructors(sort = Instr, result = k::KResult)]
#[k::precedence((Alu, Bit))]
#[rustfmt::skip]
pub enum Instruction {
    #[k::syntax("alu {op}")]
    Alu { op: Int },
    #[k::syntax("bit {index}")]
    Bit { index: Int },
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

k::equations! {
    for Decode;
    use Instruction::*;
    decode_bit: k::bits!("10 1__ bbb") => Bit(b);
}

#[k::equation]
fn decode_alu(k::term![Decode(k::bits!("1_ yyy ___"))]: Term<Instr>) -> Term<Instr> {
    Instruction::Alu(y)
}
