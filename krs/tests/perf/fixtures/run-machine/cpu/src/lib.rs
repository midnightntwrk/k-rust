//! The long-run benchmark's CPU as a cell group.
//!
//! `Cpu` is the CPU's state, and every rule here is typed by it (`for Cpu`): a rule names only
//! the CPU's cells and is a rule of every definition whose configuration holds `Cpu`.
//! This package declares no configuration.
//!
//! The CPU has eight 16-bit registers, a zero and a carry flag, and two latches, `t` and `u`,
//! through which every operand passes.
//! An instruction is an opcode byte and zero, one or two immediate bytes.
//! Its execution is a sequence of micro-operations on the computation cell, each one rewrite
//! step.
//!
//! Memory and the interrupt lines are not the CPU's.
//! A rule that needs a byte puts a request (`Bus::Read`) on the computation cell, which no rule
//! of the group consumes; the definition that holds the group answers it (`Bus::Reply`).
//! The CPU appends one event to `log` for each bus cycle.

use k::Term;
use k::builtin::{Bool, Int, KSequence, List, Map, int};

pub mod decode;

pub use decode::{
    Alu, AluOp, AluTable, Cc, Cond, Condition, Decode, Index, Instr, Instruction, Operand, Source,
    Unary, UnaryOp,
};

k::sorts! {
    BusOp: k::KItem;
    ReadDest;
    BusEvent;
    Step: k::KItem;
    MicroOp: k::KItem;
}

/// The address of the page `LoadHigh` and `StoreHigh` reach.
#[k::constant]
pub const HIGH_PAGE: Int = 0xFF00;

/// The interrupt enable register.
#[k::constant]
pub const IRQ_ENABLE: Int = 0xFFFF;

/// The interrupt request register.
#[k::constant]
pub const IRQ_REQUEST: Int = 0xFF0F;

/// The address an interrupt dispatch jumps to.
#[k::constant]
pub const IRQ_VECTOR: Int = 0x0040;

/// The register an interrupt dispatch saves `pc` in, and `JumpReg` reads.
#[k::constant]
pub const LINK: Int = 7;

/// What the CPU does with the byte a read returns.
#[k::constructors(sort = ReadDest, result = k::KResult)]
pub enum Dest {
    /// Decode it as an opcode.
    #[k::syntax("opcode")]
    Opcode,
    /// Latch it into `t`.
    #[k::syntax("intoT")]
    T,
    /// Latch it into `u`.
    #[k::syntax("intoU")]
    U,
}

/// What the CPU asks of the definition that holds it, and the answers.
#[k::constructors(sort = BusOp, result = k::KResult)]
pub enum Bus {
    /// Asked: the byte at `addr`. Answered with `Reply`.
    #[k::syntax("#busRead({addr}, {dest})")]
    Read { addr: Int, dest: ReadDest },
    /// The answer to `Read`.
    #[k::syntax("#busReply({addr}, {value}, {dest})")]
    Reply {
        addr: Int,
        value: Int,
        dest: ReadDest,
    },
    /// Asked: store `value` at `addr`. Answered by consuming the item.
    #[k::syntax("#busWrite({addr}, {value})")]
    Write { addr: Int, value: Int },
    /// Asked: the interrupt enable and request registers. Answered with `IrqLines`.
    #[k::syntax("#irqSample")]
    IrqSample,
    /// The answer to `IrqSample`.
    #[k::syntax("#irqLines({enable}, {request})")]
    IrqLines { enable: Int, request: Int },
    /// Asked: clear `bits` in the interrupt request register. Answered by consuming the item.
    #[k::syntax("#irqAck({bits})")]
    IrqAck { bits: Int },
}

/// One bus cycle, as the log records it.
#[k::constructors(sort = BusEvent, result = k::KResult)]
pub enum Event {
    #[k::syntax("read({addr}, {value})")]
    Read { addr: Int, value: Int },
    #[k::syntax("write({addr}, {value})")]
    Write { addr: Int, value: Int },
    #[k::syntax("idle")]
    Idle,
}

/// The instruction boundary.
#[k::constructors(sort = Step, result = k::KResult)]
pub enum Phase {
    /// Between two instructions.
    #[k::syntax("#boundary")]
    Boundary,
    /// The interrupt lines were asked for; the answer decides between a dispatch and a fetch.
    #[k::syntax("#decide")]
    Decide,
}

#[k::constructors(sort = MicroOp, result = k::KResult)]
pub enum Micro {
    /// Read the opcode at `pc`, advance `pc`, and decode it.
    #[k::syntax("#fetch")]
    Fetch,
    /// `t <- src`.
    #[k::syntax("#loadT({src})")]
    LoadT { src: Source },
    /// `u <- src`.
    #[k::syntax("#loadU({src})")]
    LoadU { src: Source },
    /// `t <- [addr]`.
    #[k::syntax("#readT({addr})")]
    ReadT { addr: Int },
    /// `u <- [addr]`.
    #[k::syntax("#readU({addr})")]
    ReadU { addr: Int },
    /// `t <- [HIGH_PAGE + t]`.
    #[k::syntax("#readTHigh")]
    ReadTHigh,
    /// `t <- [reg]`.
    #[k::syntax("#readTAt({reg})")]
    ReadTAt { reg: Int },
    /// `dst <- t`.
    #[k::syntax("#storeT({dst})")]
    StoreT { dst: Int },
    /// `dst <- u:t`.
    #[k::syntax("#storePair({dst})")]
    StorePair { dst: Int },
    /// `[reg] <- low byte of t`.
    #[k::syntax("#writeTAt({reg})")]
    WriteTAt { reg: Int },
    /// `[HIGH_PAGE + t] <- low byte of src`.
    #[k::syntax("#writeHigh({src})")]
    WriteHigh { src: Int },
    /// `[addr] <- value`.
    #[k::syntax("#writeByte({addr}, {value})")]
    WriteByte { addr: Int, value: Int },
    /// A bus cycle without an access.
    #[k::syntax("#idle")]
    Idle,
    /// `dst <- dst op t`, with the flags of the operation.
    #[k::syntax("#aluT({op}, {dst})")]
    AluT { op: AluOp, dst: Int },
    /// `t <- op t`, with the zero flag of the result.
    #[k::syntax("#updateT({op})")]
    UpdateT { op: UnaryOp },
    /// If `cond` holds: `pc <- pc + signed t`, taking one more cycle.
    #[k::syntax("#jumpRelativeIf({cond})")]
    JumpRelativeIf { cond: Cond },
    /// If `cond` holds: `pc <- u:t`.
    #[k::syntax("#jumpIf({cond})")]
    JumpIf { cond: Cond },
}

/// The CPU: a cell group a definition's configuration holds.
#[k::cell]
pub struct Cpu {
    #[k::cell]
    pub k: KSequence,
    /// The register file: registers 0 to 7, each a 16-bit value.
    #[k::cell]
    pub regs: Map<Int, Int>,
    #[k::cell]
    pub zero: Bool,
    #[k::cell]
    pub carry: Bool,
    #[k::cell]
    pub pc: Int,
    /// Whether interrupts are served.
    #[k::cell]
    pub ime: Bool,
    /// The operand latch, and the low byte of a two-byte immediate.
    #[k::cell]
    pub t: Int,
    /// The high byte of a two-byte immediate.
    #[k::cell]
    pub u: Int,
    /// One event per bus cycle since the start.
    #[k::cell]
    pub log: List<BusEvent>,
}

/// The low 16 bits of an integer.
#[k::function(total, internal)]
pub fn Wrap16(value: Term<Int>) -> Term<Int> {
    int::rem_euclid(value, 0x1_0000)
}

/// The low 8 bits of an integer.
#[k::function(total, internal)]
pub fn Low8(value: Term<Int>) -> Term<Int> {
    value & 0xFF
}

/// The 16-bit value of two bytes.
#[k::function(total, internal)]
pub fn Join(high: Term<Int>, low: Term<Int>) -> Term<Int> {
    Low8(high) * 0x100 + Low8(low)
}

/// The low byte of a value read as a displacement in `-128..=127`.
#[k::function(total, internal)]
pub fn Displacement(value: Term<Int>) -> Term<Int> {
    if Low8(value) < 0x80 {
        Low8(value)
    } else {
        Low8(value) - 0x100
    }
}

/// The interrupt requests that are enabled.
#[k::function(total, internal)]
pub fn Pending(enable: Term<Int>, request: Term<Int>) -> Term<Int> {
    enable & request & 0x1F
}

/// Whether the boundary dispatches an interrupt.
#[k::function(total, internal)]
pub fn Serves(ime: Term<Bool>, enable: Term<Int>, request: Term<Int>) -> Term<Bool> {
    ime && Pending(enable, request) != 0
}

/// Whether a branch condition holds for the flags.
#[k::function(total, internal)]
pub fn Holds(cond: Term<Cond>, zero: Term<Bool>, carry: Term<Bool>) -> Term<Bool>;

k::equations! {
    for Holds;
    holds_always:    (Condition::Always, _, _)       => true;
    holds_not_zero:  (Condition::NotZero, zero, _)   => !zero;
    holds_zero:      (Condition::Zero, zero, _)      => zero;
    holds_not_carry: (Condition::NotCarry, _, carry) => !carry;
    holds_carry:     (Condition::Carry, _, carry)    => carry;
}

/// The result of a two-operand operation before `Compare` discards it.
#[k::function(total, internal)]
pub fn AluRaw(op: Term<AluOp>, left: Term<Int>, right: Term<Int>) -> Term<Int>;

k::equations! {
    for AluRaw;
    raw_add:     (Alu::Add, left, right)     => Wrap16(left + right);
    raw_sub:     (Alu::Sub, left, right)     => Wrap16(left - right);
    raw_and:     (Alu::And, left, right)     => left & right;
    raw_or:      (Alu::Or, left, right)      => left | right;
    raw_xor:     (Alu::Xor, left, right)     => left ^ right;
    raw_min:     (Alu::Min, left, right)     => int::min(left, right);
    raw_max:     (Alu::Max, left, right)     => int::max(left, right);
    raw_compare: (Alu::Compare, left, right) => Wrap16(left - right);
}

/// The value a two-operand operation leaves in its destination.
#[k::function(total, internal)]
pub fn AluValue(op: Term<AluOp>, left: Term<Int>, right: Term<Int>) -> Term<Int>;

k::equations! {
    for AluValue;
    value_add:     (Alu::Add, left, right) => AluRaw(Alu::Add, left, right);
    value_sub:     (Alu::Sub, left, right) => AluRaw(Alu::Sub, left, right);
    value_and:     (Alu::And, left, right) => AluRaw(Alu::And, left, right);
    value_or:      (Alu::Or, left, right)  => AluRaw(Alu::Or, left, right);
    value_xor:     (Alu::Xor, left, right) => AluRaw(Alu::Xor, left, right);
    value_min:     (Alu::Min, left, right) => AluRaw(Alu::Min, left, right);
    value_max:     (Alu::Max, left, right) => AluRaw(Alu::Max, left, right);
    value_compare: (Alu::Compare, left, _) => left;
}

/// The carry flag a two-operand operation leaves.
#[k::function(total, internal)]
pub fn AluCarry(op: Term<AluOp>, left: Term<Int>, right: Term<Int>) -> Term<Bool>;

k::equations! {
    for AluCarry;
    carry_add:     (Alu::Add, left, right)     => left + right > 0xFFFF;
    carry_sub:     (Alu::Sub, left, right)     => left < right;
    carry_and:     (Alu::And, _, _)            => false;
    carry_or:      (Alu::Or, _, _)             => false;
    carry_xor:     (Alu::Xor, _, _)            => false;
    carry_min:     (Alu::Min, left, right)     => right < left;
    carry_max:     (Alu::Max, left, right)     => left < right;
    carry_compare: (Alu::Compare, left, right) => left < right;
}

/// The value a one-operand operation gives.
#[k::function(total, internal)]
pub fn UnaryValue(op: Term<UnaryOp>, value: Term<Int>) -> Term<Int>;

k::equations! {
    for UnaryValue;
    unary_pass:         (Unary::Pass, value)        => value;
    unary_increment:    (Unary::Increment, value)   => Wrap16(value + 1);
    unary_decrement:    (Unary::Decrement, value)   => Wrap16(value - 1);
    unary_shift_left:   (Unary::ShiftLeft, value)   => Wrap16(value << 1);
    unary_shift_right:  (Unary::ShiftRight, value)  => value >> 1;
    unary_rotate_left:  (Unary::RotateLeft, value)  => Wrap16(value << 1) | value >> 15;
    unary_rotate_right: (Unary::RotateRight, value) => value >> 1 | (value & 1) << 15;
    unary_complement:   (Unary::Complement, value)  => 0xFFFF - value;
    unary_negate:       (Unary::Negate, value)      => Wrap16(0 - value);
    unary_swap:         (Unary::Swap, value)        => Low8(value) << 8 | value >> 8;
    unary_clear:        (Unary::Clear, _)           => 0;
}

k::rules! {
    for Cpu;

    // The instruction boundary.

    boundary_sample: {
        k: [Phase::Boundary, ..],
    } => {
        k: [Bus::IrqSample, Phase::Decide, ..],
    };

    /// An enabled request is served: it is acknowledged, `pc` is saved in the link register,
    /// and the next instruction is the one at the vector.
    #[k::requires(Serves(ime, enable, request))]
    boundary_dispatch: {
        k: [Bus::IrqLines { enable, request }, Phase::Decide, ..],
        ime,
        pc,
        regs,
    } => {
        k: [Bus::IrqAck { bits: Pending(enable, request) }, Micro::Idle, Phase::Boundary, ..],
        ime: false,
        pc: IRQ_VECTOR,
        regs: k::map![LINK -> pc, ..regs],
    };

    #[k::requires(!Serves(ime, enable, request))]
    boundary_fetch: {
        k: [Bus::IrqLines { enable, request }, Phase::Decide, ..],
        ime,
    } => {
        k: [Micro::Fetch, Phase::Boundary, ..],
    };

    // Bus cycles.

    fetch: {
        k: [Micro::Fetch, ..],
        pc,
    } => {
        k: [Bus::Read { addr: pc, dest: Dest::Opcode }, ..],
        pc: Wrap16(pc + 1),
    };

    /// The opcode read: the cycle is logged and the byte decoded.
    fetched: {
        k: [Bus::Reply { addr, value, dest: Dest::Opcode }, ..],
        log,
    } => {
        k: [Decode(value), ..],
        log: [..log, Event::Read { addr, value }],
    };

    read_t: {
        k: [Micro::ReadT { addr }, ..],
    } => {
        k: [Bus::Read { addr, dest: Dest::T }, ..],
    };

    latch_t: {
        k: [Bus::Reply { addr, value, dest: Dest::T }, ..],
        t: _,
        log,
    } => {
        k: [..],
        t: value,
        log: [..log, Event::Read { addr, value }],
    };

    read_u: {
        k: [Micro::ReadU { addr }, ..],
    } => {
        k: [Bus::Read { addr, dest: Dest::U }, ..],
    };

    latch_u: {
        k: [Bus::Reply { addr, value, dest: Dest::U }, ..],
        u: _,
        log,
    } => {
        k: [..],
        u: value,
        log: [..log, Event::Read { addr, value }],
    };

    /// A write is logged and handed to the holder.
    write_byte: {
        k: [Micro::WriteByte { addr, value }, ..],
        log,
    } => {
        k: [Bus::Write { addr, value }, ..],
        log: [..log, Event::Write { addr, value }],
    };

    idle: {
        k: [Micro::Idle, ..],
        log,
    } => {
        k: [..],
        log: [..log, Event::Idle],
    };

    // Operands.

    load_t_register: {
        k: [Micro::LoadT { src: Operand::Register { index } }, ..],
        regs,
        t: _,
    } => {
        k: [..],
        t: regs[index],
    };

    load_t_immediate: {
        k: [Micro::LoadT { src: Operand::Immediate }, ..],
        pc,
    } => {
        k: [Micro::ReadT { addr: pc }, ..],
        pc: Wrap16(pc + 1),
    };

    load_u_register: {
        k: [Micro::LoadU { src: Operand::Register { index } }, ..],
        regs,
        u: _,
    } => {
        k: [..],
        u: regs[index],
    };

    load_u_immediate: {
        k: [Micro::LoadU { src: Operand::Immediate }, ..],
        pc,
    } => {
        k: [Micro::ReadU { addr: pc }, ..],
        pc: Wrap16(pc + 1),
    };

    read_t_high: {
        k: [Micro::ReadTHigh, ..],
        t,
    } => {
        k: [Micro::ReadT { addr: HIGH_PAGE + Low8(t) }, ..],
    };

    read_t_at: {
        k: [Micro::ReadTAt { reg }, ..],
        regs,
    } => {
        k: [Micro::ReadT { addr: regs[reg] }, ..],
    };

    write_t_at: {
        k: [Micro::WriteTAt { reg }, ..],
        regs,
        t,
    } => {
        k: [Micro::WriteByte { addr: regs[reg], value: Low8(t) }, ..],
    };

    write_high: {
        k: [Micro::WriteHigh { src }, ..],
        regs,
        t,
    } => {
        k: [Micro::WriteByte { addr: HIGH_PAGE + Low8(t), value: Low8(regs[src]) }, ..],
    };

    // Register transfers.

    store_t: {
        k: [Micro::StoreT { dst }, ..],
        regs,
        t,
    } => {
        k: [..],
        regs: k::map![dst -> t, ..regs],
    };

    store_pair: {
        k: [Micro::StorePair { dst }, ..],
        regs,
        t,
        u,
    } => {
        k: [..],
        regs: k::map![dst -> Join(u, t), ..regs],
    };

    alu_t: {
        k: [Micro::AluT { op, dst }, ..],
        regs,
        t,
        zero: _,
        carry: _,
    } => {
        k: [..],
        regs: k::map![dst -> AluValue(op, regs[dst], t), ..regs],
        zero: AluRaw(op, regs[dst], t) == 0,
        carry: AluCarry(op, regs[dst], t),
    };

    update_t: {
        k: [Micro::UpdateT { op }, ..],
        t,
        zero: _,
    } => {
        k: [..],
        t: UnaryValue(op, t),
        zero: UnaryValue(op, t) == 0,
    };

    // Jumps.

    #[k::requires(Holds(cond, zero, carry))]
    jump_relative_taken: {
        k: [Micro::JumpRelativeIf { cond }, ..],
        pc,
        t,
        zero,
        carry,
    } => {
        k: [Micro::Idle, ..],
        pc: Wrap16(pc + Displacement(t)),
    };

    #[k::requires(!Holds(cond, zero, carry))]
    jump_relative_not_taken: {
        k: [Micro::JumpRelativeIf { cond }, ..],
        zero,
        carry,
    } => {
        k: [..],
    };

    #[k::requires(Holds(cond, zero, carry))]
    jump_taken: {
        k: [Micro::JumpIf { cond }, ..],
        pc: _,
        t,
        u,
        zero,
        carry,
    } => {
        k: [..],
        pc: Join(u, t),
    };

    #[k::requires(!Holds(cond, zero, carry))]
    jump_not_taken: {
        k: [Micro::JumpIf { cond }, ..],
        zero,
        carry,
    } => {
        k: [..],
    };

    // Instructions: each becomes its micro-operations.

    execute_nop: {
        k: [Instruction::Nop, ..],
    } => {
        k: [..],
    };

    /// The machine stops: nothing is left to run.
    execute_stop: {
        k: [Instruction::Stop, Phase::Boundary, ..],
    } => {
        k: [..],
    };

    execute_set_ime: {
        k: [Instruction::SetIme { value }, ..],
        ime: _,
    } => {
        k: [..],
        ime: value,
    };

    execute_clear_carry: {
        k: [Instruction::ClearCarry, ..],
        carry: _,
    } => {
        k: [..],
        carry: false,
    };

    execute_load_immediate: {
        k: [Instruction::LoadImmediate { dst }, ..],
    } => {
        k: [Micro::LoadT { src: Operand::Immediate }, Micro::StoreT { dst }, ..],
    };

    execute_load_wide: {
        k: [Instruction::LoadWide { dst }, ..],
    } => {
        k: [
            Micro::LoadT { src: Operand::Immediate },
            Micro::LoadU { src: Operand::Immediate },
            Micro::StorePair { dst },
            ..,
        ],
    };

    execute_move: {
        k: [Instruction::Move { dst, src }, ..],
    } => {
        k: [Micro::LoadT { src: Operand::Register { index: src } }, Micro::StoreT { dst }, ..],
    };

    execute_update: {
        k: [Instruction::Update { op, reg }, ..],
    } => {
        k: [
            Micro::LoadT { src: Operand::Register { index: reg } },
            Micro::UpdateT { op },
            Micro::StoreT { dst: reg },
            ..,
        ],
    };

    execute_alu: {
        k: [Instruction::Arithmetic { op, dst, src }, ..],
    } => {
        k: [Micro::LoadT { src }, Micro::AluT { op, dst }, ..],
    };

    execute_alu_memory: {
        k: [Instruction::ArithmeticAt { op, dst, addr }, ..],
    } => {
        k: [Micro::ReadTAt { reg: addr }, Micro::AluT { op, dst }, ..],
    };

    execute_load_high: {
        k: [Instruction::LoadHigh { dst }, ..],
    } => {
        k: [Micro::LoadT { src: Operand::Immediate }, Micro::ReadTHigh, Micro::StoreT { dst }, ..],
    };

    execute_store_high: {
        k: [Instruction::StoreHigh { src }, ..],
    } => {
        k: [Micro::LoadT { src: Operand::Immediate }, Micro::WriteHigh { src }, ..],
    };

    execute_load_at: {
        k: [Instruction::LoadAt { dst, addr }, ..],
    } => {
        k: [Micro::ReadTAt { reg: addr }, Micro::StoreT { dst }, ..],
    };

    execute_store_at: {
        k: [Instruction::StoreAt { addr, src }, ..],
    } => {
        k: [
            Micro::LoadT { src: Operand::Register { index: src } },
            Micro::WriteTAt { reg: addr },
            ..,
        ],
    };

    execute_jump_relative: {
        k: [Instruction::JumpRelative { cond }, ..],
    } => {
        k: [Micro::LoadT { src: Operand::Immediate }, Micro::JumpRelativeIf { cond }, ..],
    };

    execute_jump: {
        k: [Instruction::Jump { cond }, ..],
    } => {
        k: [
            Micro::LoadT { src: Operand::Immediate },
            Micro::LoadU { src: Operand::Immediate },
            Micro::JumpIf { cond },
            ..,
        ],
    };

    execute_jump_register: {
        k: [Instruction::JumpRegister, ..],
        regs,
        pc: _,
    } => {
        k: [..],
        pc: regs[LINK],
    };
}
