//! Readable qualification slice for KEVM opcode execution.
//!
//! The source mapping is pinned in `../../draft/readability/kevm/README.md`.
//! The program cell uses K's builtin `Bytes` domain and decodes the selected
//! opcodes from their canonical byte values.

use k::builtin::{Bytes, Int, KSequence, bool, bytes, int};

k::sorts! {
    OpCode: k::KItem;
    WordStack;
    StatusCode;
    GasStep: k::KItem;
    Command: k::KItem;
}

#[k::constructors(sort = OpCode, result = k::KResult)]
#[k::precedence((Push, Add, ProgramCounter, Stop, Invalid, End))]
pub enum Operation {
    #[k::syntax("PUSH({width}, {value})")]
    Push { width: Int, value: Int },
    #[k::syntax("ADD")]
    Add,
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

#[k::requires(bool::and(int::ge(opcode, 2), int::le(opcode, 87)))]
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
    k::term![int::sub(
        value,
        int::mul(
            int::div(
                value,
                int::mul(
                    int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
                    int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
                ),
            ),
            int::mul(
                int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
                int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
            ),
        ),
    )]
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
        assert!(source.source().contains("<wordStack>"));
        assert!(source.source().contains("EVMC_OUT_OF_GAS"));
    }
}
