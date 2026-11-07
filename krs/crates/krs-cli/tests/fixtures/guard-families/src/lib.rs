//! The definition whose guard families `tests/guard_families.rs` reads from KRS's lowering: an
//! SM83-style decode table (inc and dec differ in bit 0, halt is the literal `118`, and ld's
//! template has the hole `op != 118`), and a function whose equations hold two templates in one
//! guard or lead a templated condition with an authored flag. The desugaring gives every token of
//! a sentence's template guards one span, the first token of its condition or its first template.

use k::Term;
use k::builtin::KSequence;
use k::builtin::bool::Bool;
use k::builtin::int::Int;

k::sorts! {
    Instr;
}

#[k::constructors(sort = Instr, result = k::KResult)]
#[k::precedence((Nop, Halt, Inc, Dec, Ld))]
#[rustfmt::skip]
pub enum Instruction {
    #[k::syntax("nop")]
    Nop,
    #[k::syntax("halt")]
    Halt,
    #[k::syntax("inc {target}")]
    Inc { target: Int },
    #[k::syntax("dec {target}")]
    Dec { target: Int },
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

k::equations! {
    for Decode;
    use Instruction::*;
    decode_nop   : 0                           => Nop;
    decode_inc_r : k::bits!("00 yyy 100")      => Inc(y);
    decode_dec_r : k::bits!("00 yyy 101")      => Dec(y);
    decode_halt  : k::bits!("01 110 110")      => Halt;
    #[k::requires(op.ne::<Int>(118))]
    decode_ld_r_r: op @ k::bits!("01 yyy zzz") => Ld(y, z);
    #[k::equation(owise)]
    decode_other : _                           => Nop;
}

/// Two templates in one guard (`pick_a`, `pick_b`), and an authored flag leading a templated
/// condition (`pick_c`).
#[k::function(total, internal)]
pub fn Pick(low: Term<Int>, high: Term<Int>, flag: Term<Bool>) -> Term<Int>;

k::equations! {
    for Pick;
    pick_a: (k::bits!("0___"), k::bits!("0___"), _) => 1;
    pick_b: (k::bits!("0___"), k::bits!("1___"), _) => 2;
    #[k::requires(flag)]
    pick_c: (k::bits!("1___"), _, flag)             => 3;
    #[k::requires(!flag)]
    pick_d: (k::bits!("1___"), _, flag)             => 4;
    #[k::equation(owise)]
    pick_other: (_, _, _)                           => 0;
}
