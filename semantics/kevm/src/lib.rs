//! Readable qualification slice for KEVM opcode execution.
//!
//! The source mapping is pinned in `../../draft/readability/kevm/README.md`.
//! The program cell uses K's builtin `Bytes` domain and decodes the selected
//! opcodes from their canonical byte values.

use k::builtin::{Bool, Bytes, Int, KSequence, bool, bytes, int};

k::sorts! {
    OpCode: k::KItem;
    WordStack;
    StatusCode;
    GasStep: k::KItem;
    Command: k::KItem;
}

#[k::constructors(sort = OpCode, result = k::KResult)]
#[k::precedence((Push, Add, Mul, Sub, Div, SignedDiv, Mod, SignedMod, AddMod, MulMod, LessThan, GreaterThan, SignedLessThan, SignedGreaterThan, Equal, IsZero, ProgramCounter, Stop, Invalid, End))]
pub enum Operation {
    #[k::syntax("PUSH({width}, {value})")]
    Push { width: Int, value: Int },
    #[k::syntax("ADD")]
    Add,
    #[k::syntax("MUL")]
    Mul,
    #[k::syntax("SUB")]
    Sub,
    #[k::syntax("DIV")]
    Div,
    #[k::syntax("SDIV")]
    SignedDiv,
    #[k::syntax("MOD")]
    Mod,
    #[k::syntax("SMOD")]
    SignedMod,
    #[k::syntax("ADDMOD")]
    AddMod,
    #[k::syntax("MULMOD")]
    MulMod,
    #[k::syntax("LT")]
    LessThan,
    #[k::syntax("GT")]
    GreaterThan,
    #[k::syntax("SLT")]
    SignedLessThan,
    #[k::syntax("SGT")]
    SignedGreaterThan,
    #[k::syntax("EQ")]
    Equal,
    #[k::syntax("ISZERO")]
    IsZero,
    #[k::syntax("PC")]
    ProgramCounter,
    #[k::syntax("STOP")]
    Stop,
    #[k::syntax("INVALID")]
    Invalid,
    #[k::syntax("#endOfProgram")]
    End,
}

#[k::constructors(sort = WordStack, result = k::KResult)]
#[k::precedence((StackEmpty, StackCons))]
pub enum Stack {
    #[k::syntax(".WordStack")]
    StackEmpty(),
    #[k::syntax("{head} : {tail}")]
    StackCons { head: Int, tail: WordStack },
}

#[k::constructors(sort = StatusCode, result = k::KResult)]
#[k::precedence((Running, Success, StackUnderflow, OutOfGas, InvalidInstruction))]
pub enum Status {
    #[k::syntax(".StatusCode")]
    Running(),
    #[k::syntax("EVMC_SUCCESS")]
    Success(),
    #[k::syntax("EVMC_STACK_UNDERFLOW")]
    StackUnderflow(),
    #[k::syntax("EVMC_OUT_OF_GAS")]
    OutOfGas(),
    #[k::syntax("EVMC_INVALID_INSTRUCTION")]
    InvalidInstruction(),
}

#[k::constructors(sort = GasStep, result = k::KResult)]
#[k::precedence((EnoughGas, InsufficientGas))]
pub enum GasResult {
    #[k::syntax("#enoughGas({op}, {remaining})")]
    EnoughGas { op: OpCode, remaining: Int },
    #[k::syntax("#insufficientGas")]
    InsufficientGas(),
}

#[k::constructors(sort = Command, result = k::KResult)]
#[k::precedence((Run))]
pub enum ExecutionCommand {
    #[k::syntax("run")]
    Run(),
}

#[k::function(total, sort = Int, syntax = "#kevmChop({value})")]
pub struct Chop {
    pub value: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmWordDiv({dividend}, {divisor})")]
pub struct WordDiv {
    pub dividend: k::Term<Int>,
    pub divisor: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmWordMod({dividend}, {divisor})")]
pub struct WordMod {
    pub dividend: k::Term<Int>,
    pub divisor: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmSign({value})")]
pub struct Sign {
    pub value: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmAbs({value})")]
pub struct Magnitude {
    pub value: k::Term<Int>,
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#kevmSignedWordDiv({dividend}, {divisor})"
)]
pub struct SignedWordDiv {
    pub dividend: k::Term<Int>,
    pub divisor: k::Term<Int>,
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#kevmSignedWordMod({dividend}, {divisor})"
)]
pub struct SignedWordMod {
    pub dividend: k::Term<Int>,
    pub divisor: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmBoolToWord({value})")]
pub struct BoolToWord {
    pub value: k::Term<Bool>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmSignedLess({left}, {right})"
)]
pub struct SignedLess {
    pub left: k::Term<Int>,
    pub right: k::Term<Int>,
}

#[k::function(total, sort = GasStep, syntax = "#kevmCharge({op}, {gas})")]
pub struct Charge {
    pub op: k::Term<OpCode>,
    pub gas: k::Term<Int>,
}

#[k::function(total, sort = OpCode, syntax = "#kevmLookup({program}, {pc})")]
pub struct Lookup {
    pub program: k::Term<Bytes>,
    pub pc: k::Term<Int>,
}

#[k::function(total, sort = OpCode, syntax = "#kevmDecode({opcode}, {program}, {pc})")]
pub struct Decode {
    pub opcode: k::Term<Int>,
    pub program: k::Term<Bytes>,
    pub pc: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmReadImmediate({program}, {at}, {remaining}, {value})")]
pub struct ReadImmediate {
    pub program: k::Term<Bytes>,
    pub at: k::Term<Int>,
    pub remaining: k::Term<Int>,
    pub value: k::Term<Int>,
}

#[k::requires(bool::and(int::ge(pc, 0), int::lt(pc, bytes::length(program))))]
#[k::equation]
fn lookup_opcode(k::term![Lookup { program, pc }]: k::Term<OpCode>) -> k::Term<OpCode> {
    k::term![Decode {
        opcode: bytes::get(program, pc),
        program,
        pc
    }]
}

#[k::requires(int::lt(pc, 0))]
#[k::equation]
fn lookup_before_program(k::term![Lookup { program, pc }]: k::Term<OpCode>) -> k::Term<OpCode> {
    k::term![Operation::End]
}

#[k::requires(int::ge(pc, bytes::length(program)))]
#[k::equation]
fn lookup_after_program(k::term![Lookup { program, pc }]: k::Term<OpCode>) -> k::Term<OpCode> {
    k::term![Operation::End]
}

#[k::equation]
fn decode_stop(
    k::term![Decode {
        opcode: 0,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Stop]
}

#[k::equation]
fn decode_add(
    k::term![Decode {
        opcode: 1,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Add]
}

#[k::equation]
fn decode_mul(
    k::term![Decode {
        opcode: 2,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Mul]
}

#[k::equation]
fn decode_sub(
    k::term![Decode {
        opcode: 3,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Sub]
}

#[k::equation]
fn decode_div(
    k::term![Decode {
        opcode: 4,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Div]
}

#[k::equation]
fn decode_signed_div(
    k::term![Decode {
        opcode: 5,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::SignedDiv]
}

#[k::equation]
fn decode_mod(
    k::term![Decode {
        opcode: 6,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Mod]
}

#[k::equation]
fn decode_signed_mod(
    k::term![Decode {
        opcode: 7,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::SignedMod]
}

#[k::equation]
fn decode_add_mod(
    k::term![Decode {
        opcode: 8,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::AddMod]
}

#[k::equation]
fn decode_mul_mod(
    k::term![Decode {
        opcode: 9,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::MulMod]
}

#[k::equation]
fn decode_less_than(
    k::term![Decode {
        opcode: 16,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::LessThan]
}

#[k::equation]
fn decode_greater_than(
    k::term![Decode {
        opcode: 17,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::GreaterThan]
}

#[k::equation]
fn decode_signed_less_than(
    k::term![Decode {
        opcode: 18,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::SignedLessThan]
}

#[k::equation]
fn decode_signed_greater_than(
    k::term![Decode {
        opcode: 19,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::SignedGreaterThan]
}

#[k::equation]
fn decode_equal(
    k::term![Decode {
        opcode: 20,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Equal]
}

#[k::equation]
fn decode_is_zero(
    k::term![Decode {
        opcode: 21,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::IsZero]
}

#[k::equation]
fn decode_pc(
    k::term![Decode {
        opcode: 88,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::ProgramCounter]
}

#[k::requires(bool::and(int::ge(opcode, 96), int::le(opcode, 127)))]
#[k::equation]
fn decode_push(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Push {
        width: int::sub(opcode, 95),
        value: ReadImmediate {
            program,
            at: int::add(pc, 1),
            remaining: int::sub(opcode, 95),
            value: 0
        }
    }]
}

#[k::requires(bool::and(int::ge(opcode, 10), int::le(opcode, 15)))]
#[k::equation]
fn decode_invalid_low(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Invalid]
}

#[k::requires(bool::and(int::ge(opcode, 22), int::le(opcode, 87)))]
#[k::equation]
fn decode_invalid_after_comparison(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Invalid]
}

#[k::requires(bool::and(int::ge(opcode, 89), int::le(opcode, 95)))]
#[k::equation]
fn decode_invalid_middle(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Invalid]
}

#[k::requires(int::ge(opcode, 128))]
#[k::equation]
fn decode_invalid_high(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Invalid]
}

#[k::requires(int::le(remaining, 0))]
#[k::equation]
fn read_immediate_done(
    k::term![ReadImmediate {
        program,
        at,
        remaining,
        value
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![value]
}

#[k::requires(int::gt(remaining, 0))]
#[k::equation]
fn read_immediate_byte(
    k::term![ReadImmediate {
        program,
        at,
        remaining,
        value
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![ReadImmediate {
        program,
        at: int::add(at, 1),
        remaining: int::sub(remaining, 1),
        value: int::add(int::mul(value, 256), bytes::get(program, at))
    }]
}

// 2^256 is written as (2^64 * 2^64)^2 so every authored Rust literal fits
// its host integer lexer while the object-language computation stays exact.
#[k::equation]
fn chop_word(k::term![Chop(value)]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::modulo(
        value,
        int::mul(
            int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
            int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
        ),
    )]
}

#[k::requires(int::eq(divisor, 0))]
#[k::equation]
fn word_div_zero(k::term![WordDiv { dividend, divisor }]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(int::ne(divisor, 0))]
#[k::equation]
fn word_div_nonzero(k::term![WordDiv { dividend, divisor }]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::div(dividend, divisor)]
}

#[k::requires(int::eq(divisor, 0))]
#[k::equation]
fn word_mod_zero(k::term![WordMod { dividend, divisor }]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(int::ne(divisor, 0))]
#[k::equation]
fn word_mod_nonzero(k::term![WordMod { dividend, divisor }]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::modulo(dividend, divisor)]
}

#[k::requires(bool::and(
    int::le(
        int::div(
            int::mul(
                int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
                int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
            ),
            2,
        ),
        value,
    ),
    int::lt(
        value,
        int::mul(
            int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
            int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
        ),
    ),
))]
#[k::equation]
fn sign_negative(k::term![Sign(value)]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::sub(0, 1)]
}

#[k::requires(bool::and(
    int::le(0, value),
    int::lt(
        value,
        int::div(
            int::mul(
                int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
                int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
            ),
            2,
        ),
    ),
))]
#[k::equation]
fn sign_nonnegative(k::term![Sign(value)]: k::Term<Int>) -> k::Term<Int> {
    k::term![1]
}

#[k::requires(bool::or(
    int::lt(value, 0),
    int::le(
        int::mul(
            int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
            int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
        ),
        value,
    ),
))]
#[k::equation]
fn sign_outside_word(k::term![Sign(value)]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(int::eq(Sign(value), int::sub(0, 1)))]
#[k::equation]
fn magnitude_negative(k::term![Magnitude(value)]: k::Term<Int>) -> k::Term<Int> {
    k::term![Chop(int::sub(0, value))]
}

#[k::requires(int::eq(Sign(value), 1))]
#[k::equation]
fn magnitude_nonnegative(k::term![Magnitude(value)]: k::Term<Int>) -> k::Term<Int> {
    k::term![value]
}

#[k::requires(int::eq(Sign(value), 0))]
#[k::equation]
fn magnitude_outside_word(k::term![Magnitude(value)]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(int::eq(int::mul(Sign(dividend), Sign(divisor)), 1,))]
#[k::equation]
fn signed_word_div_same_sign(
    k::term![SignedWordDiv { dividend, divisor }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![WordDiv {
        dividend: Magnitude(dividend),
        divisor: Magnitude(divisor)
    }]
}

#[k::requires(int::eq(int::mul(Sign(dividend), Sign(divisor)), int::sub(0, 1),))]
#[k::equation]
fn signed_word_div_different_sign(
    k::term![SignedWordDiv { dividend, divisor }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![Chop(int::sub(
        0,
        WordDiv {
            dividend: Magnitude(dividend),
            divisor: Magnitude(divisor)
        },
    ))]
}

#[k::requires(int::eq(Sign(dividend), 1))]
#[k::equation]
fn signed_word_mod_nonnegative(
    k::term![SignedWordMod { dividend, divisor }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![WordMod {
        dividend: Magnitude(dividend),
        divisor: Magnitude(divisor)
    }]
}

#[k::requires(int::eq(Sign(dividend), int::sub(0, 1)))]
#[k::equation]
fn signed_word_mod_negative(
    k::term![SignedWordMod { dividend, divisor }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![Chop(int::sub(
        0,
        WordMod {
            dividend: Magnitude(dividend),
            divisor: Magnitude(divisor)
        },
    ))]
}

#[k::equation]
fn bool_to_word_true(k::term![BoolToWord(true)]: k::Term<Int>) -> k::Term<Int> {
    k::term![1]
}

#[k::equation]
fn bool_to_word_false(k::term![BoolToWord(false)]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(int::eq(Sign(left), 1), int::eq(Sign(right), 1),))]
#[k::equation]
fn signed_less_nonnegative(k::term![SignedLess { left, right }]: k::Term<Int>) -> k::Term<Int> {
    k::term![BoolToWord(int::lt(left, right))]
}

#[k::requires(bool::and(int::eq(Sign(left), 1), int::eq(Sign(right), int::sub(0, 1)),))]
#[k::equation]
fn signed_less_positive_negative(
    k::term![SignedLess { left, right }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![BoolToWord(false)]
}

#[k::requires(bool::and(int::eq(Sign(left), int::sub(0, 1)), int::eq(Sign(right), 1),))]
#[k::equation]
fn signed_less_negative_positive(
    k::term![SignedLess { left, right }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![BoolToWord(true)]
}

#[k::requires(bool::and(
    int::eq(Sign(left), int::sub(0, 1)),
    int::eq(Sign(right), int::sub(0, 1)),
))]
#[k::equation]
fn signed_less_negative(k::term![SignedLess { left, right }]: k::Term<Int>) -> k::Term<Int> {
    k::term![BoolToWord(int::lt(Magnitude(right), Magnitude(left)))]
}

#[k::requires(int::ge(gas, 3))]
#[k::equation]
fn charge_push(
    k::term![Charge(Operation::Push { width, value }, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::Push { width, value },
        remaining: int::sub(gas, 3)
    }]
}

#[k::requires(int::lt(gas, 3))]
#[k::equation]
fn charge_push_fails(
    k::term![Charge(Operation::Push { width, value }, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 3))]
#[k::equation]
fn charge_add(k::term![Charge(Operation::Add, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::Add,
        remaining: int::sub(gas, 3)
    }]
}

#[k::requires(int::lt(gas, 3))]
#[k::equation]
fn charge_add_fails(k::term![Charge(Operation::Add, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 3))]
#[k::equation]
fn charge_sub(k::term![Charge(Operation::Sub, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::Sub,
        remaining: int::sub(gas, 3)
    }]
}

#[k::requires(int::lt(gas, 3))]
#[k::equation]
fn charge_sub_fails(k::term![Charge(Operation::Sub, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 5))]
#[k::equation]
fn charge_mul(k::term![Charge(Operation::Mul, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::Mul,
        remaining: int::sub(gas, 5)
    }]
}

#[k::requires(int::lt(gas, 5))]
#[k::equation]
fn charge_mul_fails(k::term![Charge(Operation::Mul, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 5))]
#[k::equation]
fn charge_div(k::term![Charge(Operation::Div, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::Div,
        remaining: int::sub(gas, 5)
    }]
}

#[k::requires(int::lt(gas, 5))]
#[k::equation]
fn charge_div_fails(k::term![Charge(Operation::Div, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 5))]
#[k::equation]
fn charge_signed_div(
    k::term![Charge(Operation::SignedDiv, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::SignedDiv,
        remaining: int::sub(gas, 5)
    }]
}

#[k::requires(int::lt(gas, 5))]
#[k::equation]
fn charge_signed_div_fails(
    k::term![Charge(Operation::SignedDiv, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 5))]
#[k::equation]
fn charge_mod(k::term![Charge(Operation::Mod, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::Mod,
        remaining: int::sub(gas, 5)
    }]
}

#[k::requires(int::lt(gas, 5))]
#[k::equation]
fn charge_mod_fails(k::term![Charge(Operation::Mod, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 5))]
#[k::equation]
fn charge_signed_mod(
    k::term![Charge(Operation::SignedMod, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::SignedMod,
        remaining: int::sub(gas, 5)
    }]
}

#[k::requires(int::lt(gas, 5))]
#[k::equation]
fn charge_signed_mod_fails(
    k::term![Charge(Operation::SignedMod, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 8))]
#[k::equation]
fn charge_add_mod(k::term![Charge(Operation::AddMod, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::AddMod,
        remaining: int::sub(gas, 8)
    }]
}

#[k::requires(int::lt(gas, 8))]
#[k::equation]
fn charge_add_mod_fails(
    k::term![Charge(Operation::AddMod, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 8))]
#[k::equation]
fn charge_mul_mod(k::term![Charge(Operation::MulMod, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::MulMod,
        remaining: int::sub(gas, 8)
    }]
}

#[k::requires(int::lt(gas, 8))]
#[k::equation]
fn charge_mul_mod_fails(
    k::term![Charge(Operation::MulMod, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 3))]
#[k::equation]
fn charge_less_than(
    k::term![Charge(Operation::LessThan, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::LessThan,
        remaining: int::sub(gas, 3)
    }]
}

#[k::requires(int::lt(gas, 3))]
#[k::equation]
fn charge_less_than_fails(
    k::term![Charge(Operation::LessThan, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 3))]
#[k::equation]
fn charge_greater_than(
    k::term![Charge(Operation::GreaterThan, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::GreaterThan,
        remaining: int::sub(gas, 3)
    }]
}

#[k::requires(int::lt(gas, 3))]
#[k::equation]
fn charge_greater_than_fails(
    k::term![Charge(Operation::GreaterThan, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 3))]
#[k::equation]
fn charge_signed_less_than(
    k::term![Charge(Operation::SignedLessThan, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::SignedLessThan,
        remaining: int::sub(gas, 3)
    }]
}

#[k::requires(int::lt(gas, 3))]
#[k::equation]
fn charge_signed_less_than_fails(
    k::term![Charge(Operation::SignedLessThan, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 3))]
#[k::equation]
fn charge_signed_greater_than(
    k::term![Charge(Operation::SignedGreaterThan, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::SignedGreaterThan,
        remaining: int::sub(gas, 3)
    }]
}

#[k::requires(int::lt(gas, 3))]
#[k::equation]
fn charge_signed_greater_than_fails(
    k::term![Charge(Operation::SignedGreaterThan, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 3))]
#[k::equation]
fn charge_equal(k::term![Charge(Operation::Equal, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::Equal,
        remaining: int::sub(gas, 3)
    }]
}

#[k::requires(int::lt(gas, 3))]
#[k::equation]
fn charge_equal_fails(
    k::term![Charge(Operation::Equal, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 3))]
#[k::equation]
fn charge_is_zero(k::term![Charge(Operation::IsZero, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::IsZero,
        remaining: int::sub(gas, 3)
    }]
}

#[k::requires(int::lt(gas, 3))]
#[k::equation]
fn charge_is_zero_fails(
    k::term![Charge(Operation::IsZero, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::ge(gas, 2))]
#[k::equation]
fn charge_pc(
    k::term![Charge(Operation::ProgramCounter, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::ProgramCounter,
        remaining: int::sub(gas, 2)
    }]
}

#[k::requires(int::lt(gas, 2))]
#[k::equation]
fn charge_pc_fails(
    k::term![Charge(Operation::ProgramCounter, gas)]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::equation]
fn charge_stop(k::term![Charge(Operation::Stop, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::Stop,
        remaining: gas
    }]
}

#[k::configuration]
pub struct Machine {
    #[k::cell(name = "k")]
    pub k: KSequence,
    #[k::cell(name = "program")]
    pub program: Bytes,
    #[k::cell(name = "wordStack")]
    pub word_stack: WordStack,
    #[k::cell(name = "pc")]
    pub pc: Int,
    #[k::cell(name = "gas")]
    pub gas: Int,
    #[k::cell(name = "statusCode")]
    pub status_code: StatusCode,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] command: KSequence,
        #[k::config_var(name = "PROGRAM")] program: Bytes,
        #[k::config_var(name = "STACK")] word_stack: WordStack,
        #[k::config_var(name = "PC")] pc: Int,
        #[k::config_var(name = "GAS")] gas: Int,
        #[k::config_var(name = "STATUS")] status_code: StatusCode,
    ) -> Self {
        Self {
            k: k::k![command],
            program,
            word_stack,
            pc,
            gas,
            status_code,
        }
    }
}

k::rules! {
    for Machine;
    lookup: {
        k: [ExecutionCommand::Run(), ..],
        program: program,
        pc: pc,
    } => {
        k: [crate::Lookup { program, pc }, ..],
        program: program,
        pc: pc,
    }
    where program: Bytes, pc: Int;

    begin_push: {
        k: [Operation::Push { width, value }, ..],
        gas: gas,
    } => {
        k: [crate::Charge(Operation::Push { width, value }, gas), ..],
        gas: gas,
    }
    where width: Int, value: Int, gas: Int;

    begin_add: {
        k: [Operation::Add, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::Add, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_mul: {
        k: [Operation::Mul, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::Mul, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_sub: {
        k: [Operation::Sub, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::Sub, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_div: {
        k: [Operation::Div, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::Div, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_signed_div: {
        k: [Operation::SignedDiv, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::SignedDiv, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_mod: {
        k: [Operation::Mod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::Mod, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_signed_mod: {
        k: [Operation::SignedMod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::SignedMod, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_add_mod: {
        k: [Operation::AddMod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackCons(w2, rest))),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::AddMod, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackCons(w2, rest))),
        gas: gas,
    }
    where w0: Int, w1: Int, w2: Int, rest: WordStack, gas: Int;

    begin_mul_mod: {
        k: [Operation::MulMod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackCons(w2, rest))),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::MulMod, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackCons(w2, rest))),
        gas: gas,
    }
    where w0: Int, w1: Int, w2: Int, rest: WordStack, gas: Int;

    begin_less_than: {
        k: [Operation::LessThan, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::LessThan, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_greater_than: {
        k: [Operation::GreaterThan, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::GreaterThan, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_signed_less_than: {
        k: [Operation::SignedLessThan, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::SignedLessThan, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_signed_greater_than: {
        k: [Operation::SignedGreaterThan, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::SignedGreaterThan, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_equal: {
        k: [Operation::Equal, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::Equal, gas), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_is_zero: {
        k: [Operation::IsZero, ..],
        word_stack: Stack::StackCons(w0, rest),
        gas: gas,
    } => {
        k: [crate::Charge(Operation::IsZero, gas), ..],
        word_stack: Stack::StackCons(w0, rest),
        gas: gas,
    }
    where w0: Int, rest: WordStack, gas: Int;

    begin_pc: {
        k: [Operation::ProgramCounter, ..],
        gas: gas,
    } => {
        k: [crate::Charge(Operation::ProgramCounter, gas), ..],
        gas: gas,
    }
    where gas: Int;

    begin_stop: {
        k: [Operation::Stop, ..],
        gas: gas,
    } => {
        k: [crate::Charge(Operation::Stop, gas), ..],
        gas: gas,
    }
    where gas: Int;
}

k::rules! {
    for Machine;
    exec_push: {
        k: [GasResult::EnoughGas(Operation::Push { width, value }, remaining), ..],
        word_stack: stack,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::Chop(value), stack),
        pc: int::add(pc, int::add(width, 1)),
        gas: remaining,
    }
    where remaining: Int, width: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_add: {
        k: [GasResult::EnoughGas(Operation::Add, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::Chop(int::add(w0, w1)), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_mul: {
        k: [GasResult::EnoughGas(Operation::Mul, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::Chop(int::mul(w0, w1)), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_sub: {
        k: [GasResult::EnoughGas(Operation::Sub, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::Chop(int::sub(w0, w1)), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_div: {
        k: [GasResult::EnoughGas(Operation::Div, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::WordDiv { dividend: w0, divisor: w1 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_signed_div: {
        k: [GasResult::EnoughGas(Operation::SignedDiv, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::SignedWordDiv { dividend: w0, divisor: w1 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_mod: {
        k: [GasResult::EnoughGas(Operation::Mod, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::WordMod { dividend: w0, divisor: w1 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_signed_mod: {
        k: [GasResult::EnoughGas(Operation::SignedMod, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::SignedWordMod { dividend: w0, divisor: w1 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_add_mod: {
        k: [GasResult::EnoughGas(Operation::AddMod, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackCons(w2, rest))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::WordMod { dividend: int::add(w0, w1), divisor: w2 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, w2: Int, rest: WordStack, pc: Int, gas: Int;

    exec_mul_mod: {
        k: [GasResult::EnoughGas(Operation::MulMod, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackCons(w2, rest))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::WordMod { dividend: int::mul(w0, w1), divisor: w2 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, w2: Int, rest: WordStack, pc: Int, gas: Int;

    exec_less_than: {
        k: [GasResult::EnoughGas(Operation::LessThan, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::BoolToWord(int::lt(w0, w1)), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_greater_than: {
        k: [GasResult::EnoughGas(Operation::GreaterThan, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::BoolToWord(int::gt(w0, w1)), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_signed_less_than: {
        k: [GasResult::EnoughGas(Operation::SignedLessThan, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::SignedLess { left: w0, right: w1 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_signed_greater_than: {
        k: [GasResult::EnoughGas(Operation::SignedGreaterThan, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::SignedLess { left: w1, right: w0 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_equal: {
        k: [GasResult::EnoughGas(Operation::Equal, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::BoolToWord(int::eq(w0, w1)), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_is_zero: {
        k: [GasResult::EnoughGas(Operation::IsZero, remaining), ..],
        word_stack: Stack::StackCons(w0, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::BoolToWord(int::eq(w0, 0)), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, rest: WordStack, pc: Int, gas: Int;

    exec_pc: {
        k: [GasResult::EnoughGas(Operation::ProgramCounter, remaining), ..],
        word_stack: stack,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(pc, stack),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, stack: WordStack, pc: Int, gas: Int;

    exec_stop: {
        k: [GasResult::EnoughGas(Operation::Stop, remaining), ..],
        gas: gas,
        status_code: status,
    } => {
        k: [..],
        gas: remaining,
        status_code: Status::Success(),
    }
    where remaining: Int, gas: Int, status: StatusCode;
}

k::rules! {
    for Machine;
    add_underflow_empty: {
        k: [Operation::Add, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    add_underflow_one: {
        k: [Operation::Add, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    mul_underflow_empty: {
        k: [Operation::Mul, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    mul_underflow_one: {
        k: [Operation::Mul, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    sub_underflow_empty: {
        k: [Operation::Sub, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    sub_underflow_one: {
        k: [Operation::Sub, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    div_underflow_empty: {
        k: [Operation::Div, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    div_underflow_one: {
        k: [Operation::Div, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    mod_underflow_empty: {
        k: [Operation::Mod, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    mod_underflow_one: {
        k: [Operation::Mod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    signed_div_underflow_empty: {
        k: [Operation::SignedDiv, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    signed_div_underflow_one: {
        k: [Operation::SignedDiv, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    signed_mod_underflow_empty: {
        k: [Operation::SignedMod, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    signed_mod_underflow_one: {
        k: [Operation::SignedMod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    add_mod_underflow_empty: {
        k: [Operation::AddMod, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    add_mod_underflow_one: {
        k: [Operation::AddMod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    add_mod_underflow_two: {
        k: [Operation::AddMod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, w1: Int, status: StatusCode;

    mul_mod_underflow_empty: {
        k: [Operation::MulMod, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    mul_mod_underflow_one: {
        k: [Operation::MulMod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    mul_mod_underflow_two: {
        k: [Operation::MulMod, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, w1: Int, status: StatusCode;

    less_than_underflow_empty: {
        k: [Operation::LessThan, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    less_than_underflow_one: {
        k: [Operation::LessThan, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    greater_than_underflow_empty: {
        k: [Operation::GreaterThan, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    greater_than_underflow_one: {
        k: [Operation::GreaterThan, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    signed_less_than_underflow_empty: {
        k: [Operation::SignedLessThan, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    signed_less_than_underflow_one: {
        k: [Operation::SignedLessThan, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    signed_greater_than_underflow_empty: {
        k: [Operation::SignedGreaterThan, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    signed_greater_than_underflow_one: {
        k: [Operation::SignedGreaterThan, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    equal_underflow_empty: {
        k: [Operation::Equal, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    equal_underflow_one: {
        k: [Operation::Equal, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    is_zero_underflow: {
        k: [Operation::IsZero, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    out_of_gas: {
        k: [GasResult::InsufficientGas(), ..],
        status_code: status,
    } => {
        k: [..],
        status_code: Status::OutOfGas(),
    }
    where status: StatusCode;

    invalid_instruction: {
        k: [Operation::Invalid, ..],
        status_code: status,
    } => {
        k: [..],
        status_code: Status::InvalidInstruction(),
    }
    where status: StatusCode;

    end_of_program: {
        k: [Operation::End, ..],
        status_code: status,
    } => {
        k: [..],
        status_code: Status::Success(),
    }
    where status: StatusCode;
}

/// All-path claim spanning PUSH widths, ADD, PC observation, gas, and STOP.
#[k::claim(all_paths, label = "push-add-pc-stop")]
fn push_add_pc_stop(
    k::cells! {
        k: k::configuration::KCell(ExecutionCommand::Run()),
        program: k::configuration::Cell(k::bytes!(b"\x60\x02\x60\x03\x01\x58\x00")),
        word_stack: k::configuration::Cell(Stack::StackEmpty()),
        pc: k::configuration::Cell(0),
        gas: k::configuration::Cell(11),
        status_code: k::configuration::Cell(Status::Running()),
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        program: k::configuration::Cell(k::bytes!(b"\x60\x02\x60\x03\x01\x58\x00")),
        word_stack: k::configuration::Cell(Stack::StackCons(5, Stack::StackCons(5, Stack::StackEmpty()))),
        pc: k::configuration::Cell(6),
        gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
    }
}

/// All-path claim spanning the selected arithmetic and comparison tranches.
#[k::claim(all_paths, label = "arithmetic-comparison-tranches-stop")]
fn arithmetic_comparison_tranches_stop(
    k::cells! {
        k: k::configuration::KCell(ExecutionCommand::Run()),
        program: k::configuration::Cell(k::bytes!(b"\x60\x02\x60\x07\x05\x60\x02\x60\x07\x07\x60\x05\x60\x06\x60\x04\x08\x60\x05\x60\x06\x60\x04\x09\x60\x07\x60\x02\x10\x60\x02\x60\x07\x11\x60\x07\x60\x02\x12\x60\x02\x60\x07\x13\x60\x05\x60\x05\x14\x60\x00\x15\x00")),
        word_stack: k::configuration::Cell(Stack::StackEmpty()),
        pc: k::configuration::Cell(0),
        gas: k::configuration::Cell(107),
        status_code: k::configuration::Cell(Status::Running()),
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        program: k::configuration::Cell(k::bytes!(b"\x60\x02\x60\x07\x05\x60\x02\x60\x07\x07\x60\x05\x60\x06\x60\x04\x08\x60\x05\x60\x06\x60\x04\x09\x60\x07\x60\x02\x10\x60\x02\x60\x07\x11\x60\x07\x60\x02\x12\x60\x02\x60\x07\x13\x60\x05\x60\x05\x14\x60\x00\x15\x00")),
        word_stack: k::configuration::Cell(Stack::StackCons(
            1,
            Stack::StackCons(
                1,
                Stack::StackCons(
                    1,
                    Stack::StackCons(
                        1,
                        Stack::StackCons(
                            1,
                            Stack::StackCons(
                                1,
                                Stack::StackCons(
                                    4,
                                    Stack::StackCons(
                                        0,
                                        Stack::StackCons(
                                            1,
                                            Stack::StackCons(3, Stack::StackEmpty()),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )),
        pc: k::configuration::Cell(52),
        gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use krs_compiler::{
        PackageContext, collect_host_descriptors_with_builtins, emit_k, lower_descriptor_bundle,
        lower_semantic_theory,
    };

    fn package_context() -> PackageContext {
        PackageContext::new(
            "KRS-KEVM",
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION"),
            "workspace",
            "krs_kevm_semantics",
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
        )
        .expect("valid package context")
    }

    #[test]
    fn readable_kevm_slice_collects_and_lowers_deterministically() {
        let descriptors = k::host_descriptors().collect::<Vec<_>>();
        let first = collect_host_descriptors_with_builtins(
            [package_context()],
            descriptors.clone(),
            &k::builtin_registry(),
        )
        .expect("KEVM slice lowers");
        let second = collect_host_descriptors_with_builtins(
            [package_context()],
            descriptors.into_iter().rev(),
            &k::builtin_registry(),
        )
        .expect("KEVM slice lowers twice");
        assert_eq!(
            first.to_canonical_json().unwrap(),
            second.to_canonical_json().unwrap()
        );
        let semantic = lower_descriptor_bundle(&first).expect("KEVM descriptors lower");
        let definition = lower_semantic_theory(&semantic).expect("KEVM theory lowers");
        let source = emit_k(&definition).expect("KEVM definition emits");
        let descriptors_json = first.to_canonical_json().unwrap();
        let semantic_json = semantic.to_canonical_json().unwrap();
        let definition_json = definition.definition().to_canonical_json().unwrap();
        assert!(descriptors_json.contains(r#""application": "int_mod""#));
        assert!(semantic_json.contains(r#""application": "int_mod""#));
        assert!(definition_json.contains(r#""application": "int_mod""#));
        assert!(source.source().contains(" modInt "));
        assert!(source.source().contains("<wordStack>"));
        assert!(source.source().contains("EVMC_OUT_OF_GAS"));
    }
}
