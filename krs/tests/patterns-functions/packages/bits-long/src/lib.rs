//! The long form of `krs-patterns-functions-bits`: the guards and field
//! terms its `k::bits!` templates stand for, written out. Both emit the same
//! K, byte for byte, once the sugar's hidden binder `Krs_Bits0` is renamed to
//! this package's `Op`.

use k::builtin::KSequence;
use k::builtin::int::Int;
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    Instr: Value;
    Reg: Value;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((DecodeOf, DecodeCbOf, KindOf))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("decodeOf({opcode})")]
    DecodeOf { opcode: Int },
    #[k::syntax("decodeCbOf({opcode})")]
    DecodeCbOf { opcode: Int },
    #[k::syntax("kindOf({opcode})")]
    KindOf { opcode: Int },
}

#[k::constructors(sort = Reg, result = KResult)]
#[k::precedence((B, C, D, E, H, L, Mhl, A))]
#[rustfmt::skip]
pub enum Register {
    #[k::syntax("rb")]
    B,
    #[k::syntax("rc")]
    C,
    #[k::syntax("rd")]
    D,
    #[k::syntax("re")]
    E,
    #[k::syntax("rh")]
    H,
    #[k::syntax("rl")]
    L,
    #[k::syntax("mhl")]
    Mhl,
    #[k::syntax("ra")]
    A,
}

#[k::constructors(sort = Instr, result = KResult)]
#[k::precedence((Nop, Halt, Jr, Inc, Dec, Ld, Alu, Push, Rst, Rot, Bit, Res, Set, Unknown))]
#[rustfmt::skip]
pub enum Instruction {
    #[k::syntax("nop")]
    Nop,
    #[k::syntax("halt")]
    Halt,
    #[k::syntax("jr {cond}")]
    Jr { cond: Int },
    #[k::syntax("inc {target}")]
    Inc { target: Reg },
    #[k::syntax("dec {target}")]
    Dec { target: Reg },
    #[k::syntax("ld {dst}, {src}")]
    Ld { dst: Reg, src: Reg },
    #[k::syntax("alu {op} {src}")]
    Alu { op: Int, src: Reg },
    #[k::syntax("push {pair}")]
    Push { pair: Int },
    #[k::syntax("rst {target}")]
    Rst { target: Int },
    #[k::syntax("rot {op} {target}")]
    Rot { op: Int, target: Reg },
    #[k::syntax("bit {index} {target}")]
    Bit { index: Int, target: Reg },
    #[k::syntax("res {index} {target}")]
    Res { index: Int, target: Reg },
    #[k::syntax("set {index} {target}")]
    Set { index: Int, target: Reg },
    #[k::syntax("unknown {opcode}")]
    Unknown { opcode: Int },
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

/// The 8-bit operand table `r`.
#[k::function(total, internal)]
pub fn R8(index: Term<Int>) -> Term<Reg>;

k::equations! {
    for R8;
    use Register::*;
    r8_b  : 0 => B;
    r8_c  : 1 => C;
    r8_d  : 2 => D;
    r8_e  : 3 => E;
    r8_h  : 4 => H;
    r8_l  : 5 => L;
    r8_mhl: 6 => Mhl;
    r8_a  : 7 => A;
}

/// The instruction an opcode encodes.
#[k::function(total, internal)]
pub fn Decode(opcode: Term<Int>) -> Term<Instr>;

k::equations! {
    for Decode;
    use Instruction::*;
    decode_nop    : 0      => Nop;
    decode_halt   : 118    => Halt;
    #[k::equation(owise)]
    decode_unknown: opcode => Unknown(opcode);
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(256)
        && op.bit_range::<Int>(6, 2).eq::<Int>(0)
        && op.bit_range::<Int>(5, 1).eq::<Int>(1)
        && op.bit_range::<Int>(0, 3).eq::<Int>(0)
)]
#[k::equation]
fn decode_jr_cc(k::term![Decode(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Jr(op.bit_range::<Int>(3, 2))
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(256)
        && op.bit_range::<Int>(6, 2).eq::<Int>(0)
        && op.bit_range::<Int>(0, 3).eq::<Int>(4)
)]
#[k::equation]
fn decode_inc_r(k::term![Decode(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Inc(crate::R8(op.bit_range::<Int>(3, 3)))
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(256)
        && op.bit_range::<Int>(6, 2).eq::<Int>(0)
        && op.bit_range::<Int>(0, 3).eq::<Int>(5)
)]
#[k::equation]
fn decode_dec_r(k::term![Decode(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Dec(crate::R8(op.bit_range::<Int>(3, 3)))
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(256)
        && op.bit_range::<Int>(6, 2).eq::<Int>(1)
        && op.ne::<Int>(118)
)]
#[k::equation]
fn decode_ld_r_r(k::term![Decode(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Ld(
        crate::R8(op.bit_range::<Int>(3, 3)),
        crate::R8(op.bit_range::<Int>(0, 3)),
    )
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(256)
        && op.bit_range::<Int>(6, 2).eq::<Int>(3)
        && op.bit_range::<Int>(3, 1).eq::<Int>(0)
        && op.bit_range::<Int>(0, 3).eq::<Int>(5)
)]
#[k::equation]
fn decode_push(k::term![Decode(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Push(op.bit_range::<Int>(4, 2))
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(256)
        && op.bit_range::<Int>(6, 2).eq::<Int>(3)
        && op.bit_range::<Int>(0, 3).eq::<Int>(7)
)]
#[k::equation]
fn decode_rst(k::term![Decode(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Rst(op.bit_range::<Int>(3, 3).mul::<Int>(8))
}

/// `x = 2`: `alu[y] A, r[z]`.
#[k::requires(
    op.ge::<Int>(0) && op.lt::<Int>(256) && op.bit_range::<Int>(6, 2).eq::<Int>(2)
)]
#[k::equation]
fn decode_alu(k::term![Decode(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Alu(
        op.bit_range::<Int>(3, 3),
        crate::R8(op.bit_range::<Int>(0, 3)),
    )
}

/// The instruction an opcode after the `0xCB` prefix encodes.
#[k::function(total, internal)]
pub fn DecodeCb(opcode: Term<Int>) -> Term<Instr>;

#[k::requires(
    op.ge::<Int>(0) && op.lt::<Int>(256) && op.bit_range::<Int>(6, 2).eq::<Int>(0)
)]
#[k::equation]
fn decode_cb_rot(k::term![DecodeCb(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Rot(
        op.bit_range::<Int>(3, 3),
        crate::R8(op.bit_range::<Int>(0, 3)),
    )
}

#[k::requires(
    op.ge::<Int>(0) && op.lt::<Int>(256) && op.bit_range::<Int>(6, 2).eq::<Int>(1)
)]
#[k::equation]
fn decode_cb_bit(k::term![DecodeCb(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Bit(
        op.bit_range::<Int>(3, 3),
        crate::R8(op.bit_range::<Int>(0, 3)),
    )
}

#[k::requires(
    op.ge::<Int>(0) && op.lt::<Int>(256) && op.bit_range::<Int>(6, 2).eq::<Int>(2)
)]
#[k::equation]
fn decode_cb_res(k::term![DecodeCb(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Res(
        op.bit_range::<Int>(3, 3),
        crate::R8(op.bit_range::<Int>(0, 3)),
    )
}

#[k::requires(
    op.ge::<Int>(0) && op.lt::<Int>(256) && op.bit_range::<Int>(6, 2).eq::<Int>(3)
)]
#[k::equation]
fn decode_cb_set(k::term![DecodeCb(op)]: Term<Instr>) -> Term<Instr> {
    Instruction::Set(
        op.bit_range::<Int>(3, 3),
        crate::R8(op.bit_range::<Int>(0, 3)),
    )
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    decode_of   : DecodeOf(n)   => crate::Decode(n);
    decode_cb_of: DecodeCbOf(n) => crate::DecodeCb(n);
    #[k::requires(op.ge::<Int>(0) && op.lt::<Int>(256) && op.bit_range::<Int>(7, 1).eq::<Int>(0))]
    kind_low    : KindOf(op)    => 0;
    #[k::requires(op.ge::<Int>(0) && op.lt::<Int>(256) && op.bit_range::<Int>(7, 1).eq::<Int>(1))]
    kind_high   : KindOf(op)    => 1;
}
