//! The instruction set and its decoder.
//!
//! An opcode is one byte, read as `xx yyy zzz`.
//! `Decode` is written as one equation per row of the opcode map, most of them a bit template,
//! in the order of the map.
//! The rows are disjoint and cover every byte; `benchmarks/programs/krs/run-machine/program.py`
//! holds the same map and checks both properties.

use k::Term;
use k::builtin::{Bool, Int};

k::sorts! {
    Instr: k::KItem;
    Source;
    AluOp;
    UnaryOp;
    Cond;
}

/// Where an operand comes from.
#[k::constructors(sort = Source, result = k::KResult)]
pub enum Operand {
    #[k::syntax("r{index}")]
    Register { index: Int },
    /// The byte at `pc`.
    #[k::syntax("n")]
    Immediate,
}

/// A two-operand operation.
#[k::constructors(sort = AluOp, result = k::KResult)]
pub enum Alu {
    #[k::syntax("add")]
    Add,
    #[k::syntax("sub")]
    Sub,
    #[k::syntax("and")]
    And,
    #[k::syntax("or")]
    Or,
    #[k::syntax("xor")]
    Xor,
    #[k::syntax("min")]
    Min,
    #[k::syntax("max")]
    Max,
    /// Subtract for the flags and keep the destination.
    #[k::syntax("cmp")]
    Compare,
}

/// A one-operand operation.
#[k::constructors(sort = UnaryOp, result = k::KResult)]
pub enum Unary {
    /// The value itself: `Test` reads its zero flag.
    #[k::syntax("pass")]
    Pass,
    #[k::syntax("inc")]
    Increment,
    #[k::syntax("dec")]
    Decrement,
    #[k::syntax("shl")]
    ShiftLeft,
    #[k::syntax("shr")]
    ShiftRight,
    #[k::syntax("rol")]
    RotateLeft,
    #[k::syntax("ror")]
    RotateRight,
    #[k::syntax("not")]
    Complement,
    #[k::syntax("neg")]
    Negate,
    #[k::syntax("swap")]
    Swap,
    #[k::syntax("clr")]
    Clear,
}

/// A branch condition.
#[k::constructors(sort = Cond, result = k::KResult)]
pub enum Condition {
    #[k::syntax("always")]
    Always,
    #[k::syntax("nz")]
    NotZero,
    #[k::syntax("z")]
    Zero,
    #[k::syntax("nc")]
    NotCarry,
    #[k::syntax("c")]
    Carry,
}

/// A decoded instruction.
#[k::constructors(sort = Instr, result = k::KResult)]
pub enum Instruction {
    #[k::syntax("nop")]
    Nop,
    #[k::syntax("stop")]
    Stop,
    /// `ei` and `di`.
    #[k::syntax("ime {value}")]
    SetIme { value: Bool },
    #[k::syntax("clc")]
    ClearCarry,
    /// `dst <- n`.
    #[k::syntax("li r{dst}, n")]
    LoadImmediate { dst: Int },
    /// `dst <- nn`, low byte first.
    #[k::syntax("liw r{dst}, nn")]
    LoadWide { dst: Int },
    /// `dst <- src`.
    #[k::syntax("mov r{dst}, r{src}")]
    Move { dst: Int, src: Int },
    /// `reg <- op reg`.
    #[k::syntax("{op} r{reg}")]
    Update { op: UnaryOp, reg: Int },
    /// `dst <- dst op src`.
    #[k::syntax("{op} r{dst}, {src}")]
    Arithmetic { op: AluOp, dst: Int, src: Source },
    /// `dst <- dst op [addr]`.
    #[k::syntax("{op} r{dst}, [r{addr}]")]
    ArithmeticAt { op: AluOp, dst: Int, addr: Int },
    /// `dst <- [HIGH_PAGE + n]`.
    #[k::syntax("ldh r{dst}, [n]")]
    LoadHigh { dst: Int },
    /// `[HIGH_PAGE + n] <- src`.
    #[k::syntax("sth [n], r{src}")]
    StoreHigh { src: Int },
    /// `dst <- [addr]`.
    #[k::syntax("ld r{dst}, [r{addr}]")]
    LoadAt { dst: Int, addr: Int },
    /// `[addr] <- src`.
    #[k::syntax("st [r{addr}], r{src}")]
    StoreAt { addr: Int, src: Int },
    /// `pc <- pc + signed n` if `cond` holds.
    #[k::syntax("jr {cond}, n")]
    JumpRelative { cond: Cond },
    /// `pc <- nn` if `cond` holds.
    #[k::syntax("jp {cond}, nn")]
    Jump { cond: Cond },
    /// `pc <-` the link register.
    #[k::syntax("jp link")]
    JumpRegister,
    /// A byte that encodes no instruction: no rule runs it.
    #[k::syntax("illegal {opcode}")]
    Illegal { opcode: Int },
}

/// The condition table, indexed by a 2-bit field.
#[k::function(total, internal, underspecified = "indexed by a 2-bit field")]
pub fn Cc(index: Term<Int>) -> Term<Cond>;

k::equations! {
    for Cc;
    cc_not_zero:  0 => Condition::NotZero;
    cc_zero:      1 => Condition::Zero;
    cc_not_carry: 2 => Condition::NotCarry;
    cc_carry:     3 => Condition::Carry;
}

/// The two-operand operations, indexed by a 3-bit field.
#[k::function(total, internal, underspecified = "indexed by a 3-bit field")]
pub fn AluTable(index: Term<Int>) -> Term<AluOp>;

k::equations! {
    for AluTable;
    alu_table_add:     0 => Alu::Add;
    alu_table_sub:     1 => Alu::Sub;
    alu_table_and:     2 => Alu::And;
    alu_table_or:      3 => Alu::Or;
    alu_table_xor:     4 => Alu::Xor;
    alu_table_min:     5 => Alu::Min;
    alu_table_max:     6 => Alu::Max;
    alu_table_compare: 7 => Alu::Compare;
}

/// The registers that hold an address, indexed by a 2-bit field.
#[k::function(total, internal, underspecified = "indexed by a 2-bit field")]
pub fn Index(index: Term<Int>) -> Term<Int>;

k::equations! {
    for Index;
    index_0: 0 => 4;
    index_1: 1 => 5;
    index_2: 2 => 6;
    index_3: 3 => 7;
}

/// The instruction an opcode encodes.
#[k::function(total, internal, underspecified = "defined on a byte")]
pub fn Decode(opcode: Term<Int>) -> Term<Instr>;

k::equations! {
    for Decode;
    use Instruction::*;
    // xx = 00
    decode_nop:      0x00                   => Nop;
    decode_stop:     0x08                   => Stop;
    decode_ei:       0x10                   => SetIme { value: true };
    decode_jr:       0x18                   => JumpRelative { cond: Condition::Always };
    decode_jr_cc:    k::bits!("00 1cc 000") => JumpRelative { cond: Cc(c) };
    decode_li:       k::bits!("00 rrr 001") => LoadImmediate { dst: r };
    decode_liw:      k::bits!("00 rrr 010") => LoadWide { dst: r };
    decode_inc:      k::bits!("00 rrr 011") => Update { op: Unary::Increment, reg: r };
    decode_dec:      k::bits!("00 rrr 100") => Update { op: Unary::Decrement, reg: r };
    decode_shl:      0x05                   => Update { op: Unary::ShiftLeft, reg: 0 };
    decode_shr:      0x0D                   => Update { op: Unary::ShiftRight, reg: 0 };
    decode_rol:      0x15                   => Update { op: Unary::RotateLeft, reg: 0 };
    decode_ror:      0x1D                   => Update { op: Unary::RotateRight, reg: 0 };
    decode_not:      0x25                   => Update { op: Unary::Complement, reg: 0 };
    decode_neg:      0x2D                   => Update { op: Unary::Negate, reg: 0 };
    decode_swap:     0x35                   => Update { op: Unary::Swap, reg: 0 };
    decode_clr:      0x3D                   => Update { op: Unary::Clear, reg: 0 };
    decode_ldh:      k::bits!("00 rrr 110") => LoadHigh { dst: r };
    decode_sth:      k::bits!("00 rrr 111") => StoreHigh { src: r };
    // xx = 01
    decode_di:       0x76                   => SetIme { value: false };
    /// `mov r, r` reads the register's zero flag.
    #[k::requires(d == s && d != 6)]
    decode_test:     k::bits!("01 ddd sss") => Update { op: Unary::Pass, reg: d };
    #[k::requires(d != s && d != 6 && s != 6)]
    decode_mov:      k::bits!("01 ddd sss") => Move { dst: d, src: s };
    #[k::requires(d != 6)]
    decode_mov_from: k::bits!("01 ddd 110") => LoadAt { dst: d, addr: 6 };
    #[k::requires(s != 6)]
    decode_mov_to:   k::bits!("01 110 sss") => StoreAt { addr: 6, src: s };
    // xx = 10
    #[k::requires(s != 6)]
    decode_alu:      k::bits!("10 ooo sss")
                     => Arithmetic { op: AluTable(o), dst: 0, src: Operand::Register { index: s } };
    decode_alu_at:   k::bits!("10 ooo 110") => ArithmeticAt { op: AluTable(o), dst: 0, addr: 6 };
    // xx = 11
    decode_alu_n:    k::bits!("11 ooo 000")
                     => Arithmetic { op: AluTable(o), dst: 0, src: Operand::Immediate };
    decode_load_at:  k::bits!("11 0aa 001") => LoadAt { dst: 0, addr: Index(a) };
    decode_store_at: k::bits!("11 1aa 001") => StoreAt { addr: Index(a), src: 0 };
    decode_jp_cc:    k::bits!("11 0cc 010") => Jump { cond: Cc(c) };
    decode_jp:       0xE2                   => Jump { cond: Condition::Always };
    decode_jp_link:  0xEA                   => JumpRegister;
    decode_illegal:  opcode @ 0xF2          => Illegal { opcode };
    decode_clc:      0xFA                   => ClearCarry;
    decode_add_n:    k::bits!("11 rrr 011")
                     => Arithmetic { op: Alu::Add, dst: r, src: Operand::Immediate };
    decode_sub_n:    k::bits!("11 rrr 100")
                     => Arithmetic { op: Alu::Sub, dst: r, src: Operand::Immediate };
    decode_cmp_n:    k::bits!("11 rrr 101")
                     => Arithmetic { op: Alu::Compare, dst: r, src: Operand::Immediate };
    decode_and_n:    k::bits!("11 rrr 110")
                     => Arithmetic { op: Alu::And, dst: r, src: Operand::Immediate };
    decode_xor_n:    k::bits!("11 rrr 111")
                     => Arithmetic { op: Alu::Xor, dst: r, src: Operand::Immediate };
}
