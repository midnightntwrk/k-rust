//! The long form of `krs-patterns-functions-bits`: the guards and field
//! terms its `k::bits!` templates stand for, written out. Both emit the same
//! K, byte for byte, once the sugar's hidden binder `Krs_Bits0` is renamed to
//! this package's `Op`.

use k::builtin::KSequence;
use k::builtin::bool::Bool;
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
#[k::precedence((DecodeOf, DecodeCbOf, KindOf, RegOf, EdgeOf, ImmOf))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("decodeOf({opcode})")]
    DecodeOf { opcode: Int },
    #[k::syntax("decodeCbOf({opcode})")]
    DecodeCbOf { opcode: Int },
    #[k::syntax("kindOf({opcode})")]
    KindOf { opcode: Int },
    #[k::syntax("regOf({opcode})")]
    RegOf { opcode: Int },
    #[k::syntax("edgeOf({opcode})")]
    EdgeOf { opcode: Int },
    #[k::syntax("immOf({word})")]
    ImmOf { word: Int },
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
    #[k::requires(
        op.ge::<Int>(0)
            && op.lt::<Int>(256)
            && op.bit_range::<Int>(7, 1).eq::<Int>(0)
            && op.bit_range::<Int>(3, 1).eq::<Int>(0)
    )]
    reg_low     : RegOf(op)     => crate::R8(op.bit_range::<Int>(0, 3));
    #[k::requires(op.ge::<Int>(0) && op.lt::<Int>(256) && op.bit_range::<Int>(7, 1).eq::<Int>(1))]
    reg_high: RegOf(op) => crate::Instruction::Alu(op, crate::R8(op.bit_range::<Int>(4, 3)));
    edge_of     : EdgeOf(n)     => crate::Edge(n);
    imm_of      : ImmOf(n)      => crate::Imm(n);
}

/// Whether an opcode is an 8-bit load or `halt`: the test form of the
/// `ld r, r'` template, copied with its field letters, which bind nothing.
#[k::function(total, internal)]
pub fn IsLd(opcode: Term<Int>) -> Term<Bool>;

k::equations! {
    for IsLd;
    is_ld:
        opcode => (opcode.ge::<Int>(0)
            && opcode.lt::<Int>(256)
            && opcode.bit_range::<Int>(6, 2).eq::<Int>(1));
}

/// Edge cases of the opcode grid: templates beside authored `||`
/// conditions, and tests in a condition.
#[k::function(total, internal)]
pub fn Edge(opcode: Term<Int>) -> Term<Int>;

k::equations! {
    for Edge;
    #[k::requires(
        crate::IsLd(opcode)
            && (opcode.ge::<Int>(0)
                && opcode.lt::<Int>(256)
                && opcode.bit_range::<Int>(3, 3).eq::<Int>(6))
    )]
    edge_ld_mhl: opcode => 6;
    #[k::equation(owise)]
    edge_other : opcode => 0;
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(256)
        && op.bit_range::<Int>(6, 2).eq::<Int>(0)
        && op.bit_range::<Int>(5, 1).eq::<Int>(1)
        && op.bit_range::<Int>(0, 3).eq::<Int>(0)
        && (op.bit_range::<Int>(3, 2).eq::<Int>(0) || op.bit_range::<Int>(3, 2).eq::<Int>(3))
)]
#[k::equation]
fn edge_jr(k::term![Edge(op)]: Term<Int>) -> Term<Int> {
    op.bit_range::<Int>(3, 2)
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(256)
        && op.bit_range::<Int>(6, 2).eq::<Int>(3)
        && op.bit_range::<Int>(3, 1).eq::<Int>(0)
        && op.bit_range::<Int>(0, 3).eq::<Int>(5)
        && (op.bit_range::<Int>(4, 2).eq::<Int>(0) || op.bit_range::<Int>(4, 2).eq::<Int>(3))
)]
#[k::equation]
fn edge_push(k::term![Edge(op)]: Term<Int>) -> Term<Int> {
    op.bit_range::<Int>(4, 2).add::<Int>(10)
}

/// The immediate of a RISC-V instruction word: signed, in pieces, scattered,
/// or shifted into place, as the encoding table draws each format.
#[k::function(total, internal)]
pub fn Imm(word: Term<Int>) -> Term<Int>;

k::equations! {
    for Imm;
    #[k::equation(owise)]
    imm_other: word => 0;
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(4294967296)
        && op.bit_range::<Int>(12, 3).eq::<Int>(0)
        && op.bit_range::<Int>(0, 7).eq::<Int>(19)
)]
#[k::equation]
fn imm_addi(k::term![Imm(op)]: Term<Int>) -> Term<Int> {
    op.bit_range::<Int>(20, 12)
        .sub::<Int>(op.bit_range::<Int>(31, 1).mul::<Int>(4096))
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(4294967296)
        && op.bit_range::<Int>(12, 3).eq::<Int>(2)
        && op.bit_range::<Int>(0, 7).eq::<Int>(35)
)]
#[k::equation]
fn imm_sw(k::term![Imm(op)]: Term<Int>) -> Term<Int> {
    op.bit_range::<Int>(25, 7)
        .mul::<Int>(32)
        .add::<Int>(op.bit_range::<Int>(7, 5))
        .sub::<Int>(op.bit_range::<Int>(31, 1).mul::<Int>(4096))
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(4294967296)
        && op.bit_range::<Int>(12, 3).eq::<Int>(0)
        && op.bit_range::<Int>(0, 7).eq::<Int>(99)
)]
#[k::equation]
fn imm_beq(k::term![Imm(op)]: Term<Int>) -> Term<Int> {
    op.bit_range::<Int>(31, 1)
        .mul::<Int>(4096)
        .add::<Int>(op.bit_range::<Int>(25, 6).mul::<Int>(32))
        .add::<Int>(op.bit_range::<Int>(8, 4).mul::<Int>(2))
        .add::<Int>(op.bit_range::<Int>(7, 1).mul::<Int>(2048))
        .sub::<Int>(op.bit_range::<Int>(31, 1).mul::<Int>(8192))
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(4294967296)
        && op.bit_range::<Int>(0, 7).eq::<Int>(55)
)]
#[k::equation]
fn imm_lui(k::term![Imm(op)]: Term<Int>) -> Term<Int> {
    op.bit_range::<Int>(12, 20)
        .mul::<Int>(4096)
        .sub::<Int>(op.bit_range::<Int>(31, 1).mul::<Int>(4294967296))
}

#[k::requires(
    op.ge::<Int>(0)
        && op.lt::<Int>(4294967296)
        && op.bit_range::<Int>(0, 7).eq::<Int>(111)
)]
#[k::equation]
fn imm_jal(k::term![Imm(op)]: Term<Int>) -> Term<Int> {
    op.bit_range::<Int>(31, 1)
        .mul::<Int>(1048576)
        .add::<Int>(op.bit_range::<Int>(21, 10).mul::<Int>(2))
        .add::<Int>(op.bit_range::<Int>(20, 1).mul::<Int>(2048))
        .add::<Int>(op.bit_range::<Int>(12, 8).mul::<Int>(4096))
        .sub::<Int>(op.bit_range::<Int>(31, 1).mul::<Int>(2097152))
}
