//! Bit templates: an SM83-style opcode decoder.
//!
//! The definition is pure sugar: `krs-patterns-functions-bits-long` writes the
//! guards and field terms each `k::bits!` template stands for. Both emit the
//! same K, byte for byte, once the hidden binder of an unnamed template
//! (`Krs_Bits0`) is renamed to the long form's `Op`.
//!
//! - `decodeOf(4)` is `inc rb` and `decodeOf(61)` is `dec ra`: `00 yyy 100`
//!   and `00 yyy 101` bind the field `y` and index the operand table `R8`;
//! - `decodeOf(32)` is `jr 0`: `00 1cc 000` binds the two-bit field `c`;
//! - `decodeOf(118)` is `halt`, a template without free bits (the literal
//!   `118`), and `decodeOf(65)` is `ld rb, rc`: the `op @` row excludes `118`
//!   with its own `requires`;
//! - `decodeOf(128)` is `alu 0 rb`: an `#[k::equation]` fn whose subject holds
//!   a template;
//! - `decodeOf(197)` is `push 0`, `decodeOf(255)` is `rst 56`;
//! - `decodeOf(0)` is `nop`; `decodeOf(256)`, `decodeOf(-1)`, and
//!   `decodeOf(211)` are `unknown`: a template matches only `0 <= n < 2^8`;
//! - `decodeCbOf(..)`: four templates that differ in their top two bits cover
//!   the second page;
//! - `kindOf(5)` is `0` and `kindOf(200)` is `1`: two transitions whose
//!   templates differ in the top bit, which the overlap check keeps apart.

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
    decode_nop    : 0                           => Nop;
    decode_jr_cc  : k::bits!("00 1cc 000")      => Jr(c);
    decode_inc_r  : k::bits!("00 yyy 100")      => Inc(crate::R8(y));
    decode_dec_r  : k::bits!("00 yyy 101")      => Dec(crate::R8(y));
    decode_halt   : k::bits!("01 110 110")      => Halt;
    #[k::requires(op.ne::<Int>(118))]
    decode_ld_r_r : op @ k::bits!("01 yyy zzz") => Ld(crate::R8(y), crate::R8(z));
    decode_push   : op @ k::bits!("11 pp0 101") => Push(p);
    decode_rst    : k::bits!("11 ttt 111")      => Rst(t.mul::<Int>(8));
    #[k::equation(owise)]
    decode_unknown: opcode                      => Unknown(opcode);
}

/// `x = 2`: `alu[y] A, r[z]`.
#[k::equation]
fn decode_alu(k::term![Decode(k::bits!("10 yyy zzz"))]: Term<Instr>) -> Term<Instr> {
    Instruction::Alu(y, crate::R8(z))
}

/// The instruction an opcode after the `0xCB` prefix encodes.
#[k::function(total, internal)]
pub fn DecodeCb(opcode: Term<Int>) -> Term<Instr>;

k::equations! {
    for DecodeCb;
    use Instruction::*;
    decode_cb_rot: k::bits!("00 yyy zzz") => Rot(y, crate::R8(z));
    decode_cb_bit: k::bits!("01 bbb zzz") => Bit(b, crate::R8(z));
    decode_cb_res: k::bits!("10 bbb zzz") => Res(b, crate::R8(z));
    decode_cb_set: k::bits!("11 bbb zzz") => Set(b, crate::R8(z));
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    decode_of   : DecodeOf(n)                   => crate::Decode(n);
    decode_cb_of: DecodeCbOf(n)                 => crate::DecodeCb(n);
    kind_low    : KindOf(k::bits!("0___ ____")) => 0;
    kind_high   : KindOf(k::bits!("1___ ____")) => 1;
}
