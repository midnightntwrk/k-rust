//! Readable qualification slice for KEVM opcode execution.
//!
//! The source mapping is pinned in `../../tests/kevm/source-map.md`.
//! The program cell uses K's builtin `Bytes` domain and decodes the selected
//! opcodes from their canonical byte values.

use k::builtin::{Bool, Bytes, Int, KSequence, List, Map, Set, bool, bytes, int, list, map, set};

k::sorts! {
    OpCode: k::KItem;
    WordStack;
    LogEntry;
    StatusCode;
    GasStep: k::KItem;
    PrecompileStep: k::KItem;
    CopyStep: k::KItem;
    JumpStep: k::KItem;
    Command: k::KItem;
    WorldState: k::KItem;
    G1Point: k::KItem;
    G2Point: k::KItem;
}

#[k::constructors(sort = OpCode, result = k::KResult)]
#[k::precedence((PushZero, Push, Pop, Duplicate, Swap, Add, Mul, Sub, Div, SignedDiv, Mod, SignedMod, AddMod, MulMod, Exponent, SignExtend, LessThan, GreaterThan, SignedLessThan, SignedGreaterThan, Equal, IsZero, BitAnd, BitOr, BitXor, BitNot, Byte, ShiftLeft, ShiftRight, SignedShiftRight, Sha3, Address, AccountBalance, TxOrigin, MsgCaller, MsgCallValue, CallDataLoad, CallDataSize, CallDataCopy, CodeSize, CodeCopy, TxGasPrice, ExternalCodeSize, ExternalCodeCopy, ReturnDataSize, ReturnDataCopy, ExternalCodeHash, BlockHash, BlockCoinbase, BlockTimestamp, BlockNumber, PrevRandao, BlockGasLimit, NetworkChainId, SelfBalance, BlockBaseFee, MemoryLoad, MemoryStore, MemoryStore8, StorageLoad, StorageStore, LogOpcode, MemorySize, GasRemaining, ProgramCounter, Jump, JumpIf, JumpDest, Return, Revert, StaticCall, Stop, Invalid, End))]
pub enum Operation {
    #[k::syntax("PUSHZERO")]
    PushZero,
    #[k::syntax("PUSH({width}, {value})")]
    Push { width: Int, value: Int },
    #[k::syntax("POP")]
    Pop,
    #[k::syntax("DUP({depth})")]
    Duplicate { depth: Int },
    #[k::syntax("SWAP({depth})")]
    Swap { depth: Int },
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
    #[k::syntax("EXP")]
    Exponent,
    #[k::syntax("SIGNEXTEND")]
    SignExtend,
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
    #[k::syntax("AND")]
    BitAnd,
    #[k::syntax("EVMOR")]
    BitOr,
    #[k::syntax("XOR")]
    BitXor,
    #[k::syntax("NOT")]
    BitNot,
    #[k::syntax("BYTE")]
    Byte,
    #[k::syntax("SHL")]
    ShiftLeft,
    #[k::syntax("SHR")]
    ShiftRight,
    #[k::syntax("SAR")]
    SignedShiftRight,
    #[k::syntax("SHA3")]
    Sha3,
    #[k::syntax("ADDRESS")]
    Address,
    #[k::syntax("BALANCE")]
    AccountBalance,
    #[k::syntax("ORIGIN")]
    TxOrigin,
    #[k::syntax("CALLER")]
    MsgCaller,
    #[k::syntax("CALLVALUE")]
    MsgCallValue,
    #[k::syntax("CALLDATALOAD")]
    CallDataLoad,
    #[k::syntax("CALLDATASIZE")]
    CallDataSize,
    #[k::syntax("CALLDATACOPY")]
    CallDataCopy,
    #[k::syntax("CODESIZE")]
    CodeSize,
    #[k::syntax("CODECOPY")]
    CodeCopy,
    #[k::syntax("GASPRICE")]
    TxGasPrice,
    #[k::syntax("EXTCODESIZE")]
    ExternalCodeSize,
    #[k::syntax("EXTCODECOPY")]
    ExternalCodeCopy,
    #[k::syntax("RETURNDATASIZE")]
    ReturnDataSize,
    #[k::syntax("RETURNDATACOPY")]
    ReturnDataCopy,
    #[k::syntax("EXTCODEHASH")]
    ExternalCodeHash,
    #[k::syntax("BLOCKHASH")]
    BlockHash,
    #[k::syntax("COINBASE")]
    BlockCoinbase,
    #[k::syntax("TIMESTAMP")]
    BlockTimestamp,
    #[k::syntax("NUMBER")]
    BlockNumber,
    #[k::syntax("PREVRANDAO")]
    PrevRandao,
    #[k::syntax("GASLIMIT")]
    BlockGasLimit,
    #[k::syntax("CHAINID")]
    NetworkChainId,
    #[k::syntax("SELFBALANCE")]
    SelfBalance,
    #[k::syntax("BASEFEE")]
    BlockBaseFee,
    #[k::syntax("MLOAD")]
    MemoryLoad,
    #[k::syntax("MSTORE")]
    MemoryStore,
    #[k::syntax("MSTORE8")]
    MemoryStore8,
    #[k::syntax("SLOAD")]
    StorageLoad,
    #[k::syntax("SSTORE")]
    StorageStore,
    #[k::syntax("LOG({topics})")]
    LogOpcode { topics: Int },
    #[k::syntax("MSIZE")]
    MemorySize,
    #[k::syntax("GAS")]
    GasRemaining,
    #[k::syntax("PC")]
    ProgramCounter,
    #[k::syntax("JUMP")]
    Jump,
    #[k::syntax("JUMPI")]
    JumpIf,
    #[k::syntax("JUMPDEST")]
    JumpDest,
    #[k::syntax("RETURN")]
    Return,
    #[k::syntax("REVERT")]
    Revert,
    #[k::syntax("STATICCALL")]
    StaticCall,
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

#[k::constructors(sort = LogEntry, result = k::KResult)]
#[k::precedence((Entry))]
pub enum LogRecord {
    #[k::syntax("logEntry({address}, {topics}, {data})")]
    Entry {
        address: Int,
        topics: List,
        data: Bytes,
    },
}

#[k::constructors(sort = G1Point, result = k::KResult)]
#[k::precedence((Point))]
pub enum Bn128Point {
    #[k::syntax("({x}, {y})")]
    Point { x: Int, y: Int },
}

#[k::constructors(sort = G2Point, result = k::KResult)]
#[k::precedence((G2))]
pub enum Bn128G2Point {
    #[k::syntax("({x_real} x {x_imaginary}, {y_real} x {y_imaginary})")]
    G2 {
        x_real: Int,
        x_imaginary: Int,
        y_real: Int,
        y_imaginary: Int,
    },
}

#[k::constructors(sort = StatusCode, result = k::KResult)]
#[k::precedence((Running, Success, Reverted, StackUnderflow, StackOverflow, OutOfGas, BadJumpDestination, InvalidMemoryAccess, InvalidInstruction, StaticModeViolation))]
pub enum Status {
    #[k::syntax(".StatusCode")]
    Running(),
    #[k::syntax("EVMC_SUCCESS")]
    Success(),
    #[k::syntax("EVMC_REVERT")]
    Reverted(),
    #[k::syntax("EVMC_STACK_UNDERFLOW")]
    StackUnderflow(),
    #[k::syntax("EVMC_STACK_OVERFLOW")]
    StackOverflow(),
    #[k::syntax("EVMC_OUT_OF_GAS")]
    OutOfGas(),
    #[k::syntax("EVMC_BAD_JUMP_DESTINATION")]
    BadJumpDestination(),
    #[k::syntax("EVMC_INVALID_MEMORY_ACCESS")]
    InvalidMemoryAccess(),
    #[k::syntax("EVMC_INVALID_INSTRUCTION")]
    InvalidInstruction(),
    #[k::syntax("EVMC_STATIC_MODE_VIOLATION")]
    StaticModeViolation(),
}

#[k::constructors(sort = GasStep, result = k::KResult)]
#[k::precedence((EnoughGas, EnoughEcrecPrecompileGas, EnoughSha256PrecompileGas, EnoughRipemd160PrecompileGas, EnoughIdentityPrecompileGas, EnoughModExpPrecompileGas, EnoughEcAddPrecompileGas, EnoughEcMulPrecompileGas, EnoughEcPairingPrecompileGas, InsufficientGas, StackUnderflowResult, StackOverflowResult, StaticViolationResult))]
pub enum GasResult {
    #[k::syntax("#enoughGas({op}, {remaining})")]
    EnoughGas { op: OpCode, remaining: Int },
    #[k::syntax("#enoughEcrecPrecompileGas({remaining})")]
    EnoughEcrecPrecompileGas { remaining: Int },
    #[k::syntax("#enoughSha256PrecompileGas({remaining})")]
    EnoughSha256PrecompileGas { remaining: Int },
    #[k::syntax("#enoughRipemd160PrecompileGas({remaining})")]
    EnoughRipemd160PrecompileGas { remaining: Int },
    #[k::syntax("#enoughIdentityPrecompileGas({remaining})")]
    EnoughIdentityPrecompileGas { remaining: Int },
    #[k::syntax("#enoughModExpPrecompileGas({remaining})")]
    EnoughModExpPrecompileGas { remaining: Int },
    #[k::syntax("#enoughEcAddPrecompileGas({remaining})")]
    EnoughEcAddPrecompileGas { remaining: Int },
    #[k::syntax("#enoughEcMulPrecompileGas({remaining})")]
    EnoughEcMulPrecompileGas { remaining: Int },
    #[k::syntax("#enoughEcPairingPrecompileGas({remaining})")]
    EnoughEcPairingPrecompileGas { remaining: Int },
    #[k::syntax("#insufficientGas")]
    InsufficientGas(),
    #[k::syntax("#stackUnderflow")]
    StackUnderflowResult(),
    #[k::syntax("#stackOverflow")]
    StackOverflowResult(),
    #[k::syntax("#staticViolation")]
    StaticViolationResult(),
}

#[k::constructors(sort = PrecompileStep, result = k::KResult)]
#[k::precedence((EcrecPrecompileSuccess, EcrecPrecompileFailure, Sha256PrecompileSuccess, Sha256PrecompileFailure, Ripemd160PrecompileSuccess, Ripemd160PrecompileFailure, IdentityPrecompileSuccess, IdentityPrecompileFailure, ModExpPrecompileSuccess, ModExpPrecompileFailure, EcAddPrecompileSuccess, EcAddPrecompileFailure, EcMulPrecompileSuccess, EcMulPrecompileFailure, EcPairingPrecompileSuccess, EcPairingPrecompileFailure))]
pub enum PrecompileResult {
    #[k::syntax("#ecrecPrecompileSuccess({remaining})")]
    EcrecPrecompileSuccess { remaining: Int },
    #[k::syntax("#ecrecPrecompileFailure({remaining})")]
    EcrecPrecompileFailure { remaining: Int },
    #[k::syntax("#sha256PrecompileSuccess({remaining})")]
    Sha256PrecompileSuccess { remaining: Int },
    #[k::syntax("#sha256PrecompileFailure({remaining})")]
    Sha256PrecompileFailure { remaining: Int },
    #[k::syntax("#ripemd160PrecompileSuccess({remaining})")]
    Ripemd160PrecompileSuccess { remaining: Int },
    #[k::syntax("#ripemd160PrecompileFailure({remaining})")]
    Ripemd160PrecompileFailure { remaining: Int },
    #[k::syntax("#identityPrecompileSuccess({remaining})")]
    IdentityPrecompileSuccess { remaining: Int },
    #[k::syntax("#identityPrecompileFailure({remaining})")]
    IdentityPrecompileFailure { remaining: Int },
    #[k::syntax("#modExpPrecompileSuccess({remaining})")]
    ModExpPrecompileSuccess { remaining: Int },
    #[k::syntax("#modExpPrecompileFailure({remaining})")]
    ModExpPrecompileFailure { remaining: Int },
    #[k::syntax("#ecAddPrecompileSuccess({remaining})")]
    EcAddPrecompileSuccess { remaining: Int },
    #[k::syntax("#ecAddPrecompileFailure({remaining})")]
    EcAddPrecompileFailure { remaining: Int },
    #[k::syntax("#ecMulPrecompileSuccess({remaining})")]
    EcMulPrecompileSuccess { remaining: Int },
    #[k::syntax("#ecMulPrecompileFailure({remaining})")]
    EcMulPrecompileFailure { remaining: Int },
    #[k::syntax("#ecPairingPrecompileSuccess({remaining})")]
    EcPairingPrecompileSuccess { remaining: Int },
    #[k::syntax("#ecPairingPrecompileFailure({remaining})")]
    EcPairingPrecompileFailure { remaining: Int },
}

#[k::constructors(sort = CopyStep, result = k::KResult)]
#[k::precedence((ReturnDataCopyValid, ReturnDataCopyInvalid))]
pub enum CopyResult {
    #[k::syntax("#returnDataCopyValid({remaining})")]
    ReturnDataCopyValid { remaining: Int },
    #[k::syntax("#returnDataCopyInvalid({remaining})")]
    ReturnDataCopyInvalid { remaining: Int },
}

#[k::constructors(sort = JumpStep, result = k::KResult)]
#[k::precedence((JumpValid, JumpInvalid, JumpFallthrough))]
pub enum JumpResult {
    #[k::syntax("#jumpValid({destination})")]
    JumpValid { destination: Int },
    #[k::syntax("#jumpInvalid")]
    JumpInvalid(),
    #[k::syntax("#jumpFallthrough")]
    JumpFallthrough(),
}

#[k::constructors(sort = Command, result = k::KResult)]
#[k::precedence((Run, FinishStaticCall, FinishStaticCallExceptional))]
pub enum ExecutionCommand {
    #[k::syntax("run")]
    Run(),
    #[k::syntax("#finishStaticCall({return_start}, {return_width})")]
    FinishStaticCall {
        return_start: Int,
        return_width: Int,
    },
    #[k::syntax("#finishStaticCallExceptional({return_start}, {return_width})")]
    FinishStaticCallExceptional {
        return_start: Int,
        return_width: Int,
    },
}

#[k::constructors(sort = WorldState, result = k::KResult)]
#[k::precedence((Snapshot))]
pub enum SavedWorldState {
    #[k::syntax(
        "{{ {account_id}, {balance}, {code}, {nonce}, {storage}, {original_storage} | {self_destruct}, {logs}, {refund}, {accessed_accounts}, {accessed_storage}, {created_accounts} }}"
    )]
    Snapshot {
        account_id: Int,
        balance: Int,
        code: Bytes,
        nonce: Int,
        storage: Map,
        original_storage: Map,
        self_destruct: Set,
        logs: List,
        refund: Int,
        accessed_accounts: Set,
        accessed_storage: Map,
        created_accounts: Set,
    },
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

#[k::function(total, sort = Int, syntax = "#kevmExpCost({exponent})")]
pub struct ExpCost {
    pub exponent: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmShiftLeft({value}, {shift})")]
pub struct WordShiftLeft {
    pub value: k::Term<Int>,
    pub shift: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmShiftRight({value}, {shift})")]
pub struct WordShiftRight {
    pub value: k::Term<Int>,
    pub shift: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmSignedShiftRight({value}, {shift})")]
pub struct WordSignedShiftRight {
    pub value: k::Term<Int>,
    pub shift: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmByte({index}, {value})")]
pub struct WordByte {
    pub index: k::Term<Int>,
    pub value: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmSignExtend({index}, {value})")]
pub struct WordSignExtend {
    pub index: k::Term<Int>,
    pub value: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmSignExtendByte({index}, {value})")]
pub struct SignExtendByte {
    pub index: k::Term<Int>,
    pub value: k::Term<Int>,
}

#[k::function(
    partial,
    sort = Int,
    syntax = "#kevmBlockHash({hashes}, {requested}, {highest}, {age})"
)]
pub struct BlockHashLookup {
    pub hashes: k::Term<List>,
    pub requested: k::Term<Int>,
    pub highest: k::Term<Int>,
    pub age: k::Term<Int>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmMemoryUsageUpdate({used}, {start}, {width})"
)]
pub struct MemoryUsageUpdate {
    pub used: k::Term<Int>,
    pub start: k::Term<Int>,
    pub width: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmMemoryCost({words})")]
pub struct MemoryCost {
    pub words: k::Term<Int>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmMemoryExpansionCost({used}, {start}, {width})"
)]
pub struct MemoryExpansionCost {
    pub used: k::Term<Int>,
    pub start: k::Term<Int>,
    pub width: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmCopyGasCost({used}, {start}, {width})")]
pub struct CopyGasCost {
    pub used: k::Term<Int>,
    pub start: k::Term<Int>,
    pub width: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmAccountAccessCost({accessed}, {account})")]
pub struct AccountAccessCost {
    pub accessed: k::Term<Set>,
    pub account: k::Term<Int>,
}

#[k::function(total, sort = Bool, syntax = "#kevmAccountEmpty({code}, {nonce}, {balance})")]
pub struct AccountEmpty {
    pub code: k::Term<Bytes>,
    pub nonce: k::Term<Int>,
    pub balance: k::Term<Int>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmCallMemoryUsage({used}, {argument_start}, {argument_width}, {return_start}, {return_width})"
)]
pub struct CallMemoryUsage {
    pub used: k::Term<Int>,
    pub argument_start: k::Term<Int>,
    pub argument_width: k::Term<Int>,
    pub return_start: k::Term<Int>,
    pub return_width: k::Term<Int>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmStaticCallCost({accessed}, {account}, {used}, {argument_start}, {argument_width}, {return_start}, {return_width})"
)]
pub struct StaticCallCost {
    pub accessed: k::Term<Set>,
    pub account: k::Term<Int>,
    pub used: k::Term<Int>,
    pub argument_start: k::Term<Int>,
    pub argument_width: k::Term<Int>,
    pub return_start: k::Term<Int>,
    pub return_width: k::Term<Int>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmStaticCallGas({requested}, {available})"
)]
pub struct StaticCallGas {
    pub requested: k::Term<Int>,
    pub available: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bytes,
    syntax = "#kevmEcdsaRecover({hash}, {recovery}, {r}, {s})",
    hook = krypto::ecdsa_recover,
)]
pub struct EcdsaRecover {
    pub hash: k::Term<Bytes>,
    pub recovery: k::Term<Int>,
    pub r: k::Term<Bytes>,
    pub s: k::Term<Bytes>,
}

#[k::function(total, sort = Bytes, syntax = "#kevmEcrecOutput({public_key})")]
pub struct EcrecOutput {
    pub public_key: k::Term<Bytes>,
}

#[k::function(total, sort = Bytes, syntax = "#kevmEcrecPrecompileOutput({data})")]
pub struct EcrecPrecompileOutput {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = PrecompileStep,
    syntax = "#kevmResolveEcrecPrecompile({requested}, {available})"
)]
pub struct ResolveEcrecPrecompile {
    pub requested: k::Term<Int>,
    pub available: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bytes,
    syntax = "#kevmSha256({value})",
    hook = krypto::sha256_raw,
)]
pub struct Sha256Digest {
    pub value: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmSha256PrecompileCost({data})"
)]
pub struct Sha256PrecompileCost {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = PrecompileStep,
    syntax = "#kevmResolveSha256Precompile({data}, {requested}, {available})"
)]
pub struct ResolveSha256Precompile {
    pub data: k::Term<Bytes>,
    pub requested: k::Term<Int>,
    pub available: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bytes,
    syntax = "#kevmRipemd160({value})",
    hook = krypto::ripemd160_raw,
)]
pub struct Ripemd160Digest {
    pub value: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmRipemd160PrecompileCost({data})"
)]
pub struct Ripemd160PrecompileCost {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = PrecompileStep,
    syntax = "#kevmResolveRipemd160Precompile({data}, {requested}, {available})"
)]
pub struct ResolveRipemd160Precompile {
    pub data: k::Term<Bytes>,
    pub requested: k::Term<Int>,
    pub available: k::Term<Int>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmIdentityPrecompileCost({data})"
)]
pub struct IdentityPrecompileCost {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = PrecompileStep,
    syntax = "#kevmResolveIdentityPrecompile({data}, {requested}, {available})"
)]
pub struct ResolveIdentityPrecompile {
    pub data: k::Term<Bytes>,
    pub requested: k::Term<Int>,
    pub available: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmModExpPrecompileCost({data})")]
pub struct ModExpPrecompileCost {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmModExpAdjustedExponentLength({data}, {base_length}, {exponent_length})"
)]
pub struct ModExpAdjustedExponentLength {
    pub data: k::Term<Bytes>,
    pub base_length: k::Term<Int>,
    pub exponent_length: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmModExpExponentHeadBits({value})")]
pub struct ModExpExponentHeadBits {
    pub value: k::Term<Int>,
}

#[k::function(total, sort = Bytes, syntax = "#kevmModExpPrecompileOutput({data})")]
pub struct ModExpPrecompileOutput {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = Bytes,
    syntax = "#kevmModExpOutputBody({body}, {base_length}, {exponent_length}, {modulus_length})"
)]
pub struct ModExpOutputBody {
    pub body: k::Term<Bytes>,
    pub base_length: k::Term<Int>,
    pub exponent_length: k::Term<Int>,
    pub modulus_length: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bytes,
    syntax = "#kevmModExpOutputExponent({body}, {base}, {exponent_length}, {modulus_length})"
)]
pub struct ModExpOutputExponent {
    pub body: k::Term<Bytes>,
    pub base: k::Term<Int>,
    pub exponent_length: k::Term<Int>,
    pub modulus_length: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmModExpPower({base}, {exponent}, {modulus})")]
pub struct ModExpPower {
    pub base: k::Term<Int>,
    pub exponent: k::Term<Int>,
    pub modulus: k::Term<Int>,
}

#[k::function(
    total,
    sort = PrecompileStep,
    syntax = "#kevmResolveModExpPrecompile({data}, {requested}, {available})"
)]
pub struct ResolveModExpPrecompile {
    pub data: k::Term<Bytes>,
    pub requested: k::Term<Int>,
    pub available: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bool,
    syntax = "#kevmBn128PointValid({point})",
    hook = krypto::bn128_valid,
)]
pub struct Bn128PointValid {
    pub point: k::Term<G1Point>,
}

#[k::function(
    total,
    sort = G1Point,
    syntax = "#kevmBn128Add({left}, {right})",
    hook = krypto::bn128_add,
)]
pub struct Bn128Add {
    pub left: k::Term<G1Point>,
    pub right: k::Term<G1Point>,
}

#[k::function(
    total,
    sort = G1Point,
    syntax = "#kevmBn128Mul({point}, {scalar})",
    hook = krypto::bn128_mul,
)]
pub struct Bn128Mul {
    pub point: k::Term<G1Point>,
    pub scalar: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bool,
    syntax = "#kevmBn128G2PointValid({point})",
    hook = krypto::bn128_g2_valid,
)]
pub struct Bn128G2PointValid {
    pub point: k::Term<G2Point>,
}

#[k::function(
    total,
    sort = Bool,
    syntax = "#kevmBn128Ate({g1_points}, {g2_points})",
    hook = krypto::bn128_ate,
)]
pub struct Bn128Ate {
    pub g1_points: k::Term<List>,
    pub g2_points: k::Term<List>,
}

#[k::function(total, sort = G1Point, syntax = "#kevmEcAddFirstPoint({data})")]
pub struct EcAddFirstPoint {
    pub data: k::Term<Bytes>,
}

#[k::function(total, sort = G1Point, syntax = "#kevmEcAddSecondPoint({data})")]
pub struct EcAddSecondPoint {
    pub data: k::Term<Bytes>,
}

#[k::function(total, sort = Bytes, syntax = "#kevmBn128PointBytes({point})")]
pub struct Bn128PointBytes {
    pub point: k::Term<G1Point>,
}

#[k::function(total, sort = Bytes, syntax = "#kevmEcAddPrecompileOutput({data})")]
pub struct EcAddPrecompileOutput {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = PrecompileStep,
    syntax = "#kevmResolveEcAddPrecompile({data}, {requested}, {available})"
)]
pub struct ResolveEcAddPrecompile {
    pub data: k::Term<Bytes>,
    pub requested: k::Term<Int>,
    pub available: k::Term<Int>,
}

#[k::function(total, sort = G1Point, syntax = "#kevmEcMulPoint({data})")]
pub struct EcMulPoint {
    pub data: k::Term<Bytes>,
}

#[k::function(total, sort = Int, syntax = "#kevmEcMulScalar({data})")]
pub struct EcMulScalar {
    pub data: k::Term<Bytes>,
}

#[k::function(total, sort = Bytes, syntax = "#kevmEcMulPrecompileOutput({data})")]
pub struct EcMulPrecompileOutput {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = PrecompileStep,
    syntax = "#kevmResolveEcMulPrecompile({data}, {requested}, {available})"
)]
pub struct ResolveEcMulPrecompile {
    pub data: k::Term<Bytes>,
    pub requested: k::Term<Int>,
    pub available: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmEcPairingPrecompileCost({data})")]
pub struct EcPairingPrecompileCost {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = G1Point,
    syntax = "#kevmEcPairingG1Point({data}, {index})"
)]
pub struct EcPairingG1Point {
    pub data: k::Term<Bytes>,
    pub index: k::Term<Int>,
}

#[k::function(
    total,
    sort = G2Point,
    syntax = "#kevmEcPairingG2Point({data}, {index})"
)]
pub struct EcPairingG2Point {
    pub data: k::Term<Bytes>,
    pub index: k::Term<Int>,
}

#[k::function(
    total,
    sort = List,
    syntax = "#kevmEcPairingG1Points({data}, {index}, {length})"
)]
pub struct EcPairingG1Points {
    pub data: k::Term<Bytes>,
    pub index: k::Term<Int>,
    pub length: k::Term<Int>,
}

#[k::function(
    total,
    sort = List,
    syntax = "#kevmEcPairingG2Points({data}, {index}, {length})"
)]
pub struct EcPairingG2Points {
    pub data: k::Term<Bytes>,
    pub index: k::Term<Int>,
    pub length: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bool,
    syntax = "#kevmEcPairingPointsValid({data}, {index}, {length})"
)]
pub struct EcPairingPointsValid {
    pub data: k::Term<Bytes>,
    pub index: k::Term<Int>,
    pub length: k::Term<Int>,
}

#[k::function(total, sort = Bytes, syntax = "#kevmEcPairingPrecompileOutput({data})")]
pub struct EcPairingPrecompileOutput {
    pub data: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = PrecompileStep,
    syntax = "#kevmResolveEcPairingPrecompile({data}, {requested}, {available})"
)]
pub struct ResolveEcPairingPrecompile {
    pub data: k::Term<Bytes>,
    pub requested: k::Term<Int>,
    pub available: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmMinimum({left}, {right})")]
pub struct Minimum {
    pub left: k::Term<Int>,
    pub right: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmMaximum({left}, {right})")]
pub struct Maximum {
    pub left: k::Term<Int>,
    pub right: k::Term<Int>,
}

#[k::function(total, sort = Set, syntax = "#kevmMarkAccountAccess({accessed}, {account})")]
pub struct MarkAccountAccess {
    pub accessed: k::Term<Set>,
    pub account: k::Term<Int>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmExternalCopyGasCost({accessed}, {account}, {used}, {start}, {width})"
)]
pub struct ExternalCopyGasCost {
    pub accessed: k::Term<Set>,
    pub account: k::Term<Int>,
    pub used: k::Term<Int>,
    pub start: k::Term<Int>,
    pub width: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bytes,
    syntax = "#kevmPrepareCopyMemory({memory}, {used}, {start}, {width})"
)]
pub struct PrepareCopyMemory {
    pub memory: k::Term<Bytes>,
    pub used: k::Term<Int>,
    pub start: k::Term<Int>,
    pub width: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmMemoryByte({memory}, {index})")]
pub struct MemoryByte {
    pub memory: k::Term<Bytes>,
    pub index: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bytes,
    syntax = "Keccak256raw({value})",
    hook = krypto::keccak256_raw,
)]
pub struct Keccak256Raw {
    pub value: k::Term<Bytes>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmBytesToInt({value}, {index}, {result})"
)]
pub struct BytesToInt {
    pub value: k::Term<Bytes>,
    pub index: k::Term<Int>,
    pub result: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmKeccak({value})")]
pub struct Keccak {
    pub value: k::Term<Bytes>,
}

#[k::function(total, sort = Int, syntax = "#kevmStorageValue({storage}, {index})")]
pub struct StorageValue {
    pub storage: k::Term<Map>,
    pub index: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bool,
    syntax = "#kevmStorageWarm({accessed}, {account}, {index})"
)]
pub struct StorageWarm {
    pub accessed: k::Term<Map>,
    pub account: k::Term<Int>,
    pub index: k::Term<Int>,
}

#[k::function(
    total,
    sort = Map,
    syntax = "#kevmMarkStorageAccess({accessed}, {account}, {index})"
)]
pub struct MarkStorageAccess {
    pub accessed: k::Term<Map>,
    pub account: k::Term<Int>,
    pub index: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmColdStorageSurcharge({warm})")]
pub struct ColdStorageSurcharge {
    pub warm: k::Term<Bool>,
}

#[k::function(total, sort = Int, syntax = "#kevmStorageLoadCost({warm})")]
pub struct StorageLoadCost {
    pub warm: k::Term<Bool>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmStorageStoreCost({original}, {current}, {new}, {warm})"
)]
pub struct StorageStoreCost {
    pub original: k::Term<Int>,
    pub current: k::Term<Int>,
    pub new: k::Term<Int>,
    pub warm: k::Term<Bool>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmStorageRefundDelta({original}, {current}, {new})"
)]
pub struct StorageRefundDelta {
    pub original: k::Term<Int>,
    pub current: k::Term<Int>,
    pub new: k::Term<Int>,
}

#[k::function(
    total,
    sort = GasStep,
    syntax = "#kevmPrepareStorageStore({gas}, {original}, {current}, {new}, {warm}, {static_mode})"
)]
pub struct PrepareStorageStore {
    pub gas: k::Term<Int>,
    pub original: k::Term<Int>,
    pub current: k::Term<Int>,
    pub new: k::Term<Int>,
    pub warm: k::Term<Bool>,
    pub static_mode: k::Term<Bool>,
}

#[k::function(
    total,
    sort = Int,
    syntax = "#kevmReadMemoryWord({memory}, {index}, {remaining}, {value})"
)]
pub struct ReadMemoryWord {
    pub memory: k::Term<Bytes>,
    pub index: k::Term<Int>,
    pub remaining: k::Term<Int>,
    pub value: k::Term<Int>,
}

#[k::function(
    partial,
    sort = Bytes,
    syntax = "#kevmWriteMemoryWord({memory}, {index}, {remaining}, {value})"
)]
pub struct WriteMemoryWord {
    pub memory: k::Term<Bytes>,
    pub index: k::Term<Int>,
    pub remaining: k::Term<Int>,
    pub value: k::Term<Int>,
}

#[k::function(
    partial,
    sort = Bytes,
    syntax = "#kevmCopyBytes({memory}, {destination}, {source}, {source_index}, {remaining})"
)]
pub struct CopyBytes {
    pub memory: k::Term<Bytes>,
    pub destination: k::Term<Int>,
    pub source: k::Term<Bytes>,
    pub source_index: k::Term<Int>,
    pub remaining: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bytes,
    syntax = "#kevmReturnBytes({memory}, {start}, {width})"
)]
pub struct ReturnBytes {
    pub memory: k::Term<Bytes>,
    pub start: k::Term<Int>,
    pub width: k::Term<Int>,
}

#[k::function(
    total,
    sort = CopyStep,
    syntax = "#kevmResolveReturnDataCopy({output}, {source_index}, {width}, {remaining})"
)]
pub struct ResolveReturnDataCopy {
    pub output: k::Term<Bytes>,
    pub source_index: k::Term<Int>,
    pub width: k::Term<Int>,
    pub remaining: k::Term<Int>,
}

#[k::function(total, sort = Int, syntax = "#kevmStackSize({stack})")]
pub struct StackSize {
    pub stack: k::Term<WordStack>,
}

#[k::function(partial, sort = Int, syntax = "#kevmStackAt({stack}, {index})")]
pub struct StackAt {
    pub stack: k::Term<WordStack>,
    pub index: k::Term<Int>,
}

#[k::function(
    partial,
    sort = WordStack,
    syntax = "#kevmStackSet({stack}, {index}, {value})"
)]
pub struct StackSet {
    pub stack: k::Term<WordStack>,
    pub index: k::Term<Int>,
    pub value: k::Term<Int>,
}

#[k::function(total, sort = List, syntax = "#kevmStackTakeList({stack}, {remaining})")]
pub struct StackTakeList {
    pub stack: k::Term<WordStack>,
    pub remaining: k::Term<Int>,
}

#[k::function(total, sort = WordStack, syntax = "#kevmStackDrop({stack}, {remaining})")]
pub struct StackDrop {
    pub stack: k::Term<WordStack>,
    pub remaining: k::Term<Int>,
}

#[k::function(
    partial,
    sort = GasStep,
    syntax = "#kevmPrepareStack({op}, {stack}, {gas})"
)]
pub struct PrepareStack {
    pub op: k::Term<OpCode>,
    pub stack: k::Term<WordStack>,
    pub gas: k::Term<Int>,
}

#[k::function(
    total,
    sort = GasStep,
    syntax = "#kevmPreparePush({op}, {stack}, {gas}, {cost})"
)]
pub struct PreparePush {
    pub op: k::Term<OpCode>,
    pub stack: k::Term<WordStack>,
    pub gas: k::Term<Int>,
    pub cost: k::Term<Int>,
}

#[k::function(
    total,
    sort = GasStep,
    syntax = "#kevmPrepareLog({op}, {stack}, {gas}, {used}, {static_mode})"
)]
pub struct PrepareLog {
    pub op: k::Term<OpCode>,
    pub stack: k::Term<WordStack>,
    pub gas: k::Term<Int>,
    pub used: k::Term<Int>,
    pub static_mode: k::Term<Bool>,
}

#[k::function(
    total,
    sort = GasStep,
    syntax = "#kevmPrepareStaticCall({stack}, {accessed}, {used}, {gas})"
)]
pub struct PrepareStaticCall {
    pub stack: k::Term<WordStack>,
    pub accessed: k::Term<Set>,
    pub used: k::Term<Int>,
    pub gas: k::Term<Int>,
}

#[k::function(total, sort = GasStep, syntax = "#kevmCharge({op}, {gas})")]
pub struct Charge {
    pub op: k::Term<OpCode>,
    pub gas: k::Term<Int>,
}

#[k::function(
    total,
    sort = GasStep,
    syntax = "#kevmChargeFixed({op}, {gas}, {cost})"
)]
pub struct ChargeFixed {
    pub op: k::Term<OpCode>,
    pub gas: k::Term<Int>,
    pub cost: k::Term<Int>,
}

#[k::function(
    total,
    sort = GasStep,
    syntax = "#kevmChargeStaticCall({gas}, {cost}, {account})"
)]
pub struct ChargeStaticCall {
    pub gas: k::Term<Int>,
    pub cost: k::Term<Int>,
    pub account: k::Term<Int>,
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

#[k::function(
    total,
    sort = Bool,
    syntax = "#kevmValidJumpDestination({program}, {destination})"
)]
pub struct ValidJumpDestination {
    pub program: k::Term<Bytes>,
    pub destination: k::Term<Int>,
}

#[k::function(
    total,
    sort = Bool,
    syntax = "#kevmScanJumpDestination({program}, {destination}, {cursor})"
)]
pub struct ScanJumpDestination {
    pub program: k::Term<Bytes>,
    pub destination: k::Term<Int>,
    pub cursor: k::Term<Int>,
}

#[k::function(total, sort = JumpStep, syntax = "#kevmResolveJump({program}, {destination})")]
pub struct ResolveJump {
    pub program: k::Term<Bytes>,
    pub destination: k::Term<Int>,
}

#[k::function(
    total,
    sort = JumpStep,
    syntax = "#kevmResolveJumpIf({program}, {destination}, {condition})"
)]
pub struct ResolveJumpIf {
    pub program: k::Term<Bytes>,
    pub destination: k::Term<Int>,
    pub condition: k::Term<Int>,
}

#[k::requires(map::in_keys(index, storage))]
#[k::equation]
fn storage_value_present(k::term![StorageValue { storage, index }]: k::Term<Int>) -> k::Term<Int> {
    k::term![map::get(storage, index)]
}

#[k::requires(bool::not(map::in_keys(index, storage)))]
#[k::equation]
fn storage_value_absent(k::term![StorageValue { storage, index }]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(map::in_keys(account, accessed))]
#[k::equation]
fn storage_warm_present(
    k::term![StorageWarm {
        accessed,
        account,
        index
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![set::contains(index, map::get(accessed, account))]
}

#[k::requires(bool::not(map::in_keys(account, accessed)))]
#[k::equation]
fn storage_warm_absent(
    k::term![StorageWarm {
        accessed,
        account,
        index
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![false]
}

#[k::requires(map::in_keys(account, accessed))]
#[k::equation]
fn mark_storage_access_present(
    k::term![MarkStorageAccess {
        accessed,
        account,
        index
    }]: k::Term<Map>,
) -> k::Term<Map> {
    k::term![map::update(
        accessed,
        account,
        set::concat(map::get(accessed, account), set::item(index))
    )]
}

#[k::requires(bool::not(map::in_keys(account, accessed)))]
#[k::equation]
fn mark_storage_access_absent(
    k::term![MarkStorageAccess {
        accessed,
        account,
        index
    }]: k::Term<Map>,
) -> k::Term<Map> {
    k::term![map::update(accessed, account, set::item(index))]
}

#[k::equation]
fn cold_storage_surcharge_warm(
    k::term![ColdStorageSurcharge { warm: true }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn cold_storage_surcharge_cold(
    k::term![ColdStorageSurcharge { warm: false }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![2100]
}

#[k::equation]
fn storage_load_cost_warm(k::term![StorageLoadCost { warm: true }]: k::Term<Int>) -> k::Term<Int> {
    k::term![100]
}

#[k::equation]
fn storage_load_cost_cold(k::term![StorageLoadCost { warm: false }]: k::Term<Int>) -> k::Term<Int> {
    k::term![2100]
}

#[k::requires(int::eq(current, new))]
#[k::equation]
fn storage_store_cost_unchanged(
    k::term![StorageStoreCost {
        original,
        current,
        new,
        warm
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(100, ColdStorageSurcharge(warm))]
}

#[k::requires(bool::and(
    int::ne(current, new),
    bool::and(int::eq(original, current), int::eq(original, 0)),
))]
#[k::equation]
fn storage_store_cost_set(
    k::term![StorageStoreCost {
        original,
        current,
        new,
        warm
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(20000, ColdStorageSurcharge(warm))]
}

#[k::requires(bool::and(
    int::ne(current, new),
    bool::and(int::eq(original, current), int::ne(original, 0)),
))]
#[k::equation]
fn storage_store_cost_reset(
    k::term![StorageStoreCost {
        original,
        current,
        new,
        warm
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(2900, ColdStorageSurcharge(warm))]
}

#[k::requires(bool::and(int::ne(current, new), int::ne(original, current)))]
#[k::equation]
fn storage_store_cost_dirty(
    k::term![StorageStoreCost {
        original,
        current,
        new,
        warm
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(100, ColdStorageSurcharge(warm))]
}

#[k::requires(int::eq(current, new))]
#[k::equation]
fn storage_refund_unchanged(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(
    int::ne(current, new),
    bool::and(
        int::eq(original, current),
        bool::and(int::ne(original, 0), int::eq(new, 0)),
    ),
))]
#[k::equation]
fn storage_refund_clean_clear(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![4800]
}

#[k::requires(bool::and(
    int::ne(current, new),
    bool::and(
        int::eq(original, current),
        bool::or(int::eq(original, 0), int::ne(new, 0)),
    ),
))]
#[k::equation]
fn storage_refund_clean_no_clear(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(
    int::ne(original, current),
    bool::and(int::eq(original, 0), int::eq(new, original)),
))]
#[k::equation]
fn storage_refund_restore_new_slot(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![19900]
}

#[k::requires(bool::and(
    int::ne(current, new),
    bool::and(
        int::ne(original, current),
        bool::and(int::eq(original, 0), int::ne(new, original)),
    ),
))]
#[k::equation]
fn storage_refund_dirty_new_slot(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(
    int::ne(original, current),
    bool::and(
        int::ne(original, 0),
        bool::and(int::eq(current, 0), int::eq(new, original)),
    ),
))]
#[k::equation]
fn storage_refund_restore_cleared_slot(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::sub(0, 2000)]
}

#[k::requires(bool::and(
    int::ne(current, new),
    bool::and(
        int::ne(original, current),
        bool::and(
            int::ne(original, 0),
            bool::and(int::eq(current, 0), int::ne(new, original)),
        ),
    ),
))]
#[k::equation]
fn storage_refund_rewrite_cleared_slot(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::sub(0, 4800)]
}

#[k::requires(bool::and(
    int::ne(original, current),
    bool::and(int::ne(original, 0), bool::and(int::ne(current, 0), int::eq(new, 0)),),
))]
#[k::equation]
fn storage_refund_clear_dirty_slot(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![4800]
}

#[k::requires(bool::and(
    int::ne(original, current),
    bool::and(
        int::ne(original, 0),
        bool::and(int::ne(current, 0), int::eq(new, original)),
    ),
))]
#[k::equation]
fn storage_refund_restore_dirty_slot(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![2800]
}

#[k::requires(bool::and(
    int::ne(current, new),
    bool::and(
        int::ne(original, current),
        bool::and(
            int::ne(original, 0),
            bool::and(
                int::ne(current, 0),
                bool::and(int::ne(new, 0), int::ne(new, original)),
            ),
        ),
    ),
))]
#[k::equation]
fn storage_refund_other_dirty_slot(
    k::term![StorageRefundDelta {
        original,
        current,
        new
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn prepare_storage_store_static(
    k::term![PrepareStorageStore {
        gas,
        original,
        current,
        new,
        warm,
        static_mode: true
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::StaticViolationResult()]
}

#[k::requires(int::le(gas, 2300))]
#[k::equation]
fn prepare_storage_store_stipend(
    k::term![PrepareStorageStore {
        gas,
        original,
        current,
        new,
        warm,
        static_mode: false
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::requires(int::gt(gas, 2300))]
#[k::equation]
fn prepare_storage_store_allowed(
    k::term![PrepareStorageStore {
        gas,
        original,
        current,
        new,
        warm,
        static_mode: false
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![ChargeFixed {
        op: Operation::StorageStore,
        gas,
        cost: StorageStoreCost {
            original,
            current,
            new,
            warm
        }
    }]
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
fn decode_exponent(
    k::term![Decode {
        opcode: 10,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Exponent]
}

#[k::equation]
fn decode_sign_extend(
    k::term![Decode {
        opcode: 11,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::SignExtend]
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
fn decode_bit_and(
    k::term![Decode {
        opcode: 22,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BitAnd]
}

#[k::equation]
fn decode_bit_or(
    k::term![Decode {
        opcode: 23,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BitOr]
}

#[k::equation]
fn decode_bit_xor(
    k::term![Decode {
        opcode: 24,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BitXor]
}

#[k::equation]
fn decode_bit_not(
    k::term![Decode {
        opcode: 25,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BitNot]
}

#[k::equation]
fn decode_byte(
    k::term![Decode {
        opcode: 26,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Byte]
}

#[k::equation]
fn decode_shift_left(
    k::term![Decode {
        opcode: 27,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::ShiftLeft]
}

#[k::equation]
fn decode_shift_right(
    k::term![Decode {
        opcode: 28,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::ShiftRight]
}

#[k::equation]
fn decode_signed_shift_right(
    k::term![Decode {
        opcode: 29,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::SignedShiftRight]
}

#[k::equation]
fn decode_sha3(
    k::term![Decode {
        opcode: 32,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Sha3]
}

#[k::equation]
fn decode_address(
    k::term![Decode {
        opcode: 48,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Address]
}

#[k::equation]
fn decode_balance(
    k::term![Decode {
        opcode: 49,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::AccountBalance]
}

#[k::equation]
fn decode_origin(
    k::term![Decode {
        opcode: 50,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::TxOrigin]
}

#[k::equation]
fn decode_caller(
    k::term![Decode {
        opcode: 51,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::MsgCaller]
}

#[k::equation]
fn decode_call_value(
    k::term![Decode {
        opcode: 52,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::MsgCallValue]
}

#[k::equation]
fn decode_call_data_load(
    k::term![Decode {
        opcode: 53,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::CallDataLoad]
}

#[k::equation]
fn decode_call_data_size(
    k::term![Decode {
        opcode: 54,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::CallDataSize]
}

#[k::equation]
fn decode_call_data_copy(
    k::term![Decode {
        opcode: 55,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::CallDataCopy]
}

#[k::equation]
fn decode_code_size(
    k::term![Decode {
        opcode: 56,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::CodeSize]
}

#[k::equation]
fn decode_code_copy(
    k::term![Decode {
        opcode: 57,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::CodeCopy]
}

#[k::equation]
fn decode_gas_price(
    k::term![Decode {
        opcode: 58,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::TxGasPrice]
}

#[k::equation]
fn decode_external_code_size(
    k::term![Decode {
        opcode: 59,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::ExternalCodeSize]
}

#[k::equation]
fn decode_external_code_copy(
    k::term![Decode {
        opcode: 60,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::ExternalCodeCopy]
}

#[k::equation]
fn decode_return_data_size(
    k::term![Decode {
        opcode: 61,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::ReturnDataSize]
}

#[k::equation]
fn decode_return_data_copy(
    k::term![Decode {
        opcode: 62,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::ReturnDataCopy]
}

#[k::equation]
fn decode_external_code_hash(
    k::term![Decode {
        opcode: 63,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::ExternalCodeHash]
}

#[k::equation]
fn decode_block_hash(
    k::term![Decode {
        opcode: 64,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BlockHash]
}

#[k::equation]
fn decode_coinbase(
    k::term![Decode {
        opcode: 65,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BlockCoinbase]
}

#[k::equation]
fn decode_timestamp(
    k::term![Decode {
        opcode: 66,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BlockTimestamp]
}

#[k::equation]
fn decode_number(
    k::term![Decode {
        opcode: 67,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BlockNumber]
}

#[k::equation]
fn decode_prev_randao(
    k::term![Decode {
        opcode: 68,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::PrevRandao]
}

#[k::equation]
fn decode_gas_limit(
    k::term![Decode {
        opcode: 69,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BlockGasLimit]
}

#[k::equation]
fn decode_chain_id(
    k::term![Decode {
        opcode: 70,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::NetworkChainId]
}

#[k::equation]
fn decode_self_balance(
    k::term![Decode {
        opcode: 71,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::SelfBalance]
}

#[k::equation]
fn decode_base_fee(
    k::term![Decode {
        opcode: 72,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::BlockBaseFee]
}

#[k::equation]
fn decode_memory_load(
    k::term![Decode {
        opcode: 81,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::MemoryLoad]
}

#[k::equation]
fn decode_memory_store(
    k::term![Decode {
        opcode: 82,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::MemoryStore]
}

#[k::equation]
fn decode_memory_store8(
    k::term![Decode {
        opcode: 83,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::MemoryStore8]
}

#[k::equation]
fn decode_storage_load(
    k::term![Decode {
        opcode: 84,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::StorageLoad]
}

#[k::equation]
fn decode_storage_store(
    k::term![Decode {
        opcode: 85,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::StorageStore]
}

#[k::equation]
fn decode_memory_size(
    k::term![Decode {
        opcode: 89,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::MemorySize]
}

#[k::equation]
fn decode_gas_remaining(
    k::term![Decode {
        opcode: 90,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::GasRemaining]
}

#[k::equation]
fn decode_pop(
    k::term![Decode {
        opcode: 80,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Pop]
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

#[k::equation]
fn decode_jump(
    k::term![Decode {
        opcode: 86,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Jump]
}

#[k::equation]
fn decode_jump_if(
    k::term![Decode {
        opcode: 87,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::JumpIf]
}

#[k::equation]
fn decode_jump_dest(
    k::term![Decode {
        opcode: 91,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::JumpDest]
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

#[k::requires(bool::and(int::ge(opcode, 128), int::le(opcode, 143)))]
#[k::equation]
fn decode_duplicate(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Duplicate {
        depth: int::sub(opcode, 127)
    }]
}

#[k::requires(bool::and(int::ge(opcode, 144), int::le(opcode, 159)))]
#[k::equation]
fn decode_swap(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Swap {
        depth: int::sub(opcode, 143)
    }]
}

#[k::equation]
fn decode_push_zero(
    k::term![Decode {
        opcode: 95,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::PushZero]
}

#[k::requires(bool::and(int::ge(opcode, 160), int::le(opcode, 164)))]
#[k::equation]
fn decode_log(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::LogOpcode {
        topics: int::sub(opcode, 160)
    }]
}

#[k::requires(bool::and(int::ge(opcode, 12), int::le(opcode, 15)))]
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

#[k::requires(bool::or(
    bool::and(
        bool::and(int::ge(opcode, 30), int::le(opcode, 47)),
        int::ne(opcode, 32),
    ),
    bool::and(int::ge(opcode, 73), int::le(opcode, 79)),
))]
#[k::equation]
fn decode_invalid_context_gaps(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Invalid]
}

#[k::requires(bool::and(int::ge(opcode, 92), int::le(opcode, 94)))]
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

#[k::equation]
fn decode_return(
    k::term![Decode {
        opcode: 243,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Return]
}

#[k::equation]
fn decode_revert(
    k::term![Decode {
        opcode: 253,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Revert]
}

#[k::equation]
fn decode_static_call(
    k::term![Decode {
        opcode: 250,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::StaticCall]
}

#[k::requires(bool::and(int::ge(opcode, 165), int::le(opcode, 242)))]
#[k::equation]
fn decode_invalid_high_before_return(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Invalid]
}

#[k::requires(bool::and(
    bool::and(int::ge(opcode, 244), int::le(opcode, 252)),
    int::ne(opcode, 250),
))]
#[k::equation]
fn decode_invalid_high_between_return_and_revert(
    k::term![Decode {
        opcode,
        program,
        pc
    }]: k::Term<OpCode>,
) -> k::Term<OpCode> {
    k::term![Operation::Invalid]
}

#[k::requires(int::ge(opcode, 254))]
#[k::equation]
fn decode_invalid_high_after_revert(
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

#[k::requires(int::le(width, 0))]
#[k::equation]
fn memory_usage_nonpositive_width(
    k::term![MemoryUsageUpdate { used, start, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![used]
}

#[k::requires(bool::and(
    int::gt(width, 0),
    int::ge(used, int::div(int::add(int::add(start, width), 31), 32)),
))]
#[k::equation]
fn memory_usage_unchanged(
    k::term![MemoryUsageUpdate { used, start, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![used]
}

#[k::requires(bool::and(
    int::gt(width, 0),
    int::lt(used, int::div(int::add(int::add(start, width), 31), 32)),
))]
#[k::equation]
fn memory_usage_grows(
    k::term![MemoryUsageUpdate { used, start, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::div(int::add(int::add(start, width), 31), 32)]
}

#[k::equation]
fn memory_cost(k::term![MemoryCost(words)]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::add(
        int::mul(3, words),
        int::div(int::mul(words, words), 512),
    )]
}

#[k::equation]
fn memory_expansion_cost(
    k::term![MemoryExpansionCost { used, start, width }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::sub(
        MemoryCost(MemoryUsageUpdate { used, start, width }),
        MemoryCost(used),
    )]
}

#[k::equation]
fn copy_gas_cost(k::term![CopyGasCost { used, start, width }]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::add(
        MemoryExpansionCost { used, start, width },
        int::add(3, int::mul(3, int::div(int::add(width, 31), 32)),),
    )]
}

#[k::requires(set::contains(account, accessed))]
#[k::equation]
fn account_access_cost_warm(
    k::term![AccountAccessCost { accessed, account }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![100]
}

#[k::requires(bool::not(set::contains(account, accessed)))]
#[k::equation]
fn account_access_cost_cold(
    k::term![AccountAccessCost { accessed, account }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![2600]
}

#[k::equation]
fn account_empty(
    k::term![AccountEmpty {
        code,
        nonce,
        balance
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![bool::and(
        int::eq(bytes::length(code), 0),
        bool::and(int::eq(nonce, 0), int::eq(balance, 0)),
    )]
}

#[k::equation]
fn call_memory_usage(
    k::term![CallMemoryUsage {
        used,
        argument_start,
        argument_width,
        return_start,
        return_width
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![MemoryUsageUpdate {
        used: MemoryUsageUpdate {
            used,
            start: argument_start,
            width: argument_width
        },
        start: return_start,
        width: return_width
    }]
}

#[k::equation]
fn static_call_cost(
    k::term![StaticCallCost {
        accessed,
        account,
        used,
        argument_start,
        argument_width,
        return_start,
        return_width
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(
        AccountAccessCost { accessed, account },
        int::sub(
            MemoryCost(CallMemoryUsage {
                used,
                argument_start,
                argument_width,
                return_start,
                return_width
            }),
            MemoryCost(used),
        ),
    )]
}

#[k::equation]
fn mark_account_access(
    k::term![MarkAccountAccess { accessed, account }]: k::Term<Set>,
) -> k::Term<Set> {
    k::term![set::concat(accessed, set::item(account))]
}

#[k::equation]
fn external_copy_gas_cost(
    k::term![ExternalCopyGasCost {
        accessed,
        account,
        used,
        start,
        width
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(
        AccountAccessCost { accessed, account },
        int::add(
            MemoryExpansionCost { used, start, width },
            int::mul(3, int::div(int::add(width, 31), 32)),
        ),
    )]
}

#[k::requires(int::le(width, 0))]
#[k::equation]
fn prepare_copy_memory_zero_width(
    k::term![PrepareCopyMemory {
        memory,
        used,
        start,
        width
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![memory]
}

#[k::requires(int::gt(width, 0))]
#[k::equation]
fn prepare_copy_memory_positive_width(
    k::term![PrepareCopyMemory {
        memory,
        used,
        start,
        width
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![bytes::pad_right(
        memory,
        int::mul(MemoryUsageUpdate { used, start, width }, 32),
        0,
    )]
}

#[k::requires(bool::and(int::ge(index, 0), int::lt(index, bytes::length(memory)),))]
#[k::equation]
fn memory_byte_present(k::term![MemoryByte { memory, index }]: k::Term<Int>) -> k::Term<Int> {
    k::term![bytes::get(memory, index)]
}

#[k::requires(bool::or(int::lt(index, 0), int::ge(index, bytes::length(memory)),))]
#[k::equation]
fn memory_byte_absent(k::term![MemoryByte { memory, index }]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::or(int::lt(index, 0), int::ge(index, bytes::length(value)),))]
#[k::equation]
fn bytes_to_int_done(
    k::term![BytesToInt {
        value,
        index,
        result
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![result]
}

#[k::requires(bool::and(int::ge(index, 0), int::lt(index, bytes::length(value)),))]
#[k::equation]
fn bytes_to_int_byte(
    k::term![BytesToInt {
        value,
        index,
        result
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![BytesToInt {
        value,
        index: int::add(index, 1),
        result: int::add(int::mul(result, 256), bytes::get(value, index))
    }]
}

#[k::equation]
fn keccak(k::term![Keccak(value)]: k::Term<Int>) -> k::Term<Int> {
    k::term![BytesToInt {
        value: Keccak256Raw(value),
        index: 0,
        result: 0
    }]
}

#[k::requires(int::le(remaining, 0))]
#[k::equation]
fn read_memory_word_done(
    k::term![ReadMemoryWord {
        memory,
        index,
        remaining,
        value
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![value]
}

#[k::requires(int::gt(remaining, 0))]
#[k::equation]
fn read_memory_word_byte(
    k::term![ReadMemoryWord {
        memory,
        index,
        remaining,
        value
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![ReadMemoryWord {
        memory,
        index: int::add(index, 1),
        remaining: int::sub(remaining, 1),
        value: int::add(int::mul(value, 256), MemoryByte { memory, index })
    }]
}

#[k::requires(int::le(remaining, 0))]
#[k::equation]
fn write_memory_word_done(
    k::term![WriteMemoryWord {
        memory,
        index,
        remaining,
        value
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![memory]
}

#[k::requires(int::gt(remaining, 0))]
#[k::equation]
fn write_memory_word_byte(
    k::term![WriteMemoryWord {
        memory,
        index,
        remaining,
        value
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![WriteMemoryWord {
        memory: bytes::update(
            memory,
            int::add(index, int::sub(remaining, 1)),
            int::modulo(value, 256),
        ),
        index,
        remaining: int::sub(remaining, 1),
        value: int::div(value, 256)
    }]
}

#[k::requires(int::le(remaining, 0))]
#[k::equation]
fn copy_bytes_done(
    k::term![CopyBytes {
        memory,
        destination,
        source,
        source_index,
        remaining
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![memory]
}

#[k::requires(int::gt(remaining, 0))]
#[k::equation]
fn copy_bytes_step(
    k::term![CopyBytes {
        memory,
        destination,
        source,
        source_index,
        remaining
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![CopyBytes {
        memory: bytes::update(
            memory,
            destination,
            MemoryByte {
                memory: source,
                index: source_index
            },
        ),
        destination: int::add(destination, 1),
        source,
        source_index: int::add(source_index, 1),
        remaining: int::sub(remaining, 1)
    }]
}

#[k::equation]
fn return_bytes(
    k::term![ReturnBytes {
        memory,
        start,
        width
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![CopyBytes {
        memory: bytes::pad_right(bytes::empty(), width, 0),
        destination: 0,
        source: memory,
        source_index: start,
        remaining: width
    }]
}

#[k::requires(int::le(int::add(source_index, width), bytes::length(output)))]
#[k::equation]
fn resolve_return_data_copy_valid(
    k::term![ResolveReturnDataCopy {
        output,
        source_index,
        width,
        remaining
    }]: k::Term<CopyStep>,
) -> k::Term<CopyStep> {
    k::term![CopyResult::ReturnDataCopyValid { remaining }]
}

#[k::requires(int::gt(int::add(source_index, width), bytes::length(output)))]
#[k::equation]
fn resolve_return_data_copy_invalid(
    k::term![ResolveReturnDataCopy {
        output,
        source_index,
        width,
        remaining
    }]: k::Term<CopyStep>,
) -> k::Term<CopyStep> {
    k::term![CopyResult::ReturnDataCopyInvalid { remaining }]
}

#[k::requires(bool::or(int::lt(destination, 0), int::ge(destination, bytes::length(program)),))]
#[k::equation]
fn invalid_jump_destination_outside_program(
    k::term![ValidJumpDestination {
        program,
        destination
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![false]
}

#[k::requires(bool::and(int::ge(destination, 0), int::lt(destination, bytes::length(program)),))]
#[k::equation]
fn scan_jump_destination(
    k::term![ValidJumpDestination {
        program,
        destination
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![ScanJumpDestination {
        program,
        destination,
        cursor: 0
    }]
}

#[k::requires(int::gt(cursor, destination))]
#[k::equation]
fn scan_jump_destination_skipped(
    k::term![ScanJumpDestination {
        program,
        destination,
        cursor
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![false]
}

#[k::requires(int::eq(cursor, destination))]
#[k::equation]
fn scan_jump_destination_found(
    k::term![ScanJumpDestination {
        program,
        destination,
        cursor
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![int::eq(bytes::get(program, cursor), 91)]
}

#[k::requires(bool::and(
    int::lt(cursor, destination),
    bool::and(
        int::ge(bytes::get(program, cursor), 96),
        int::le(bytes::get(program, cursor), 127),
    ),
))]
#[k::equation]
fn scan_jump_destination_past_push(
    k::term![ScanJumpDestination {
        program,
        destination,
        cursor
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![ScanJumpDestination {
        program,
        destination,
        cursor: int::add(cursor, int::sub(bytes::get(program, cursor), 94),)
    }]
}

#[k::requires(bool::and(
    int::lt(cursor, destination),
    bool::or(
        int::lt(bytes::get(program, cursor), 96),
        int::gt(bytes::get(program, cursor), 127),
    ),
))]
#[k::equation]
fn scan_jump_destination_past_opcode(
    k::term![ScanJumpDestination {
        program,
        destination,
        cursor
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![ScanJumpDestination {
        program,
        destination,
        cursor: int::add(cursor, 1)
    }]
}

#[k::requires(bool::eq(
    ValidJumpDestination {
        program,
        destination
    },
    true,
))]
#[k::equation]
fn resolve_valid_jump(
    k::term![ResolveJump {
        program,
        destination
    }]: k::Term<JumpStep>,
) -> k::Term<JumpStep> {
    k::term![JumpResult::JumpValid { destination }]
}

#[k::requires(bool::eq(
    ValidJumpDestination {
        program,
        destination
    },
    false,
))]
#[k::equation]
fn resolve_invalid_jump(
    k::term![ResolveJump {
        program,
        destination
    }]: k::Term<JumpStep>,
) -> k::Term<JumpStep> {
    k::term![JumpResult::JumpInvalid()]
}

#[k::requires(int::eq(condition, 0))]
#[k::equation]
fn resolve_false_jump_if(
    k::term![ResolveJumpIf {
        program,
        destination,
        condition
    }]: k::Term<JumpStep>,
) -> k::Term<JumpStep> {
    k::term![JumpResult::JumpFallthrough()]
}

#[k::requires(int::ne(condition, 0))]
#[k::equation]
fn resolve_true_jump_if(
    k::term![ResolveJumpIf {
        program,
        destination,
        condition
    }]: k::Term<JumpStep>,
) -> k::Term<JumpStep> {
    k::term![ResolveJump {
        program,
        destination
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

#[k::requires(int::le(exponent, 0))]
#[k::equation]
fn exp_cost_zero(k::term![ExpCost(exponent)]: k::Term<Int>) -> k::Term<Int> {
    k::term![10]
}

#[k::requires(int::gt(exponent, 0))]
#[k::equation]
fn exp_cost_positive(k::term![ExpCost(exponent)]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::add(
        10,
        int::mul(50, int::add(int::div(int::log2(exponent), 8), 1)),
    )]
}

#[k::requires(bool::and(bool::and(int::ge(value, 0), int::ge(shift, 0)), int::lt(shift, 256),))]
#[k::equation]
fn shift_left_word(k::term![WordShiftLeft { value, shift }]: k::Term<Int>) -> k::Term<Int> {
    k::term![Chop(int::shift_left(value, shift))]
}

#[k::requires(bool::or(int::lt(value, 0), bool::or(int::lt(shift, 0), int::ge(shift, 256)),))]
#[k::equation]
fn shift_left_outside_word(k::term![WordShiftLeft { value, shift }]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(bool::and(int::ge(value, 0), int::ge(shift, 0)), int::lt(shift, 256),))]
#[k::equation]
fn shift_right_word(k::term![WordShiftRight { value, shift }]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::shift_right(value, shift)]
}

#[k::requires(bool::or(int::lt(value, 0), bool::or(int::lt(shift, 0), int::ge(shift, 256)),))]
#[k::equation]
fn shift_right_outside_word(
    k::term![WordShiftRight { value, shift }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(bool::and(int::ge(value, 0), int::ge(shift, 0)), int::lt(shift, 256),))]
#[k::equation]
fn signed_shift_right_word(
    k::term![WordSignedShiftRight { value, shift }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![Chop(int::shift_right(
        int::mul(Magnitude(value), Sign(value)),
        shift,
    ))]
}

#[k::requires(bool::and(
    bool::and(int::ge(value, 0), int::ge(shift, 256)),
    int::eq(Sign(value), int::sub(0, 1)),
))]
#[k::equation]
fn signed_shift_right_large_negative(
    k::term![WordSignedShiftRight { value, shift }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::sub(
        int::mul(
            int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
            int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),
        ),
        1,
    )]
}

#[k::requires(bool::and(
    bool::and(int::ge(value, 0), int::ge(shift, 256)),
    int::ne(Sign(value), int::sub(0, 1)),
))]
#[k::equation]
fn signed_shift_right_large_nonnegative(
    k::term![WordSignedShiftRight { value, shift }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::or(int::lt(value, 0), int::lt(shift, 0)))]
#[k::equation]
fn signed_shift_right_outside_word(
    k::term![WordSignedShiftRight { value, shift }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(int::ge(index, 0), int::lt(index, 32)))]
#[k::equation]
fn byte_in_word(k::term![WordByte { index, value }]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::modulo(
        int::shift_right(value, int::mul(8, int::sub(31, index))),
        256,
    )]
}

#[k::requires(bool::or(int::lt(index, 0), int::ge(index, 32)))]
#[k::equation]
fn byte_outside_word(k::term![WordByte { index, value }]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn sign_extend_byte(k::term![SignExtendByte { index, value }]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::modulo(
        int::shift_right(value, int::mul(8, index)),
        256
    )]
}

#[k::requires(bool::or(int::lt(index, 0), int::ge(index, 32)))]
#[k::equation]
fn sign_extend_invalid(k::term![WordSignExtend { index, value }]: k::Term<Int>) -> k::Term<Int> {
    k::term![value]
}

#[k::requires(bool::and(
    bool::and(int::ge(index, 0), int::lt(index, 32)),
    int::lt(SignExtendByte { index, value }, 128),
))]
#[k::equation]
fn sign_extend_positive(k::term![WordSignExtend { index, value }]: k::Term<Int>) -> k::Term<Int> {
    k::term![Chop(int::bit_and(
        int::sub(int::shift_left(1, int::mul(8, int::add(index, 1))), 1),
        value,
    ))]
}

#[k::requires(bool::and(
    bool::and(int::ge(index, 0), int::lt(index, 32)),
    int::ge(SignExtendByte { index, value }, 128),
))]
#[k::equation]
fn sign_extend_negative(k::term![WordSignExtend { index, value }]: k::Term<Int>) -> k::Term<Int> {
    k::term![Chop(int::bit_or(
        int::bit_xor(
            int::sub(
                int::mul(
                    int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616,),
                    int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616,),
                ),
                1,
            ),
            int::sub(int::shift_left(1, int::mul(8, int::add(index, 1))), 1),
        ),
        value,
    ))]
}

#[k::requires(int::gt(requested, highest))]
#[k::equation]
fn block_hash_future(
    k::term![BlockHashLookup {
        hashes,
        requested,
        highest,
        age
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(int::le(requested, highest), int::ge(age, 256)))]
#[k::equation]
fn block_hash_too_old(
    k::term![BlockHashLookup {
        hashes,
        requested,
        highest,
        age
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(
    bool::and(int::le(requested, highest), int::lt(age, 256)),
    bool::and(int::lt(age, list::size(hashes)), int::eq(list::get(hashes, age), 0)),
))]
#[k::equation]
fn block_hash_zero_sentinel(
    k::term![BlockHashLookup {
        hashes,
        requested,
        highest,
        age
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(bool::and(
    bool::and(int::eq(requested, highest), int::lt(age, 256)),
    bool::and(int::lt(age, list::size(hashes)), int::ne(list::get(hashes, age), 0)),
))]
#[k::equation]
fn block_hash_found(
    k::term![BlockHashLookup {
        hashes,
        requested,
        highest,
        age
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![list::get(hashes, age)]
}

#[k::requires(bool::and(
    bool::and(int::lt(requested, highest), int::lt(age, 256)),
    bool::and(int::lt(age, list::size(hashes)), int::ne(list::get(hashes, age), 0)),
))]
#[k::equation]
fn block_hash_continue(
    k::term![BlockHashLookup {
        hashes,
        requested,
        highest,
        age
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![BlockHashLookup {
        hashes,
        requested,
        highest: int::sub(highest, 1),
        age: int::add(age, 1)
    }]
}

#[k::equation]
fn stack_size_empty(k::term![StackSize(Stack::StackEmpty())]: k::Term<Int>) -> k::Term<Int> {
    k::term![0]
}

#[k::equation]
fn stack_size_cons(
    k::term![StackSize(Stack::StackCons(head, tail))]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(1, StackSize(tail))]
}

#[k::requires(int::le(index, 0))]
#[k::equation]
fn stack_at_here(
    k::term![StackAt {
        stack: Stack::StackCons(head, tail),
        index
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![head]
}

#[k::requires(int::gt(index, 0))]
#[k::equation]
fn stack_at_later(
    k::term![StackAt {
        stack: Stack::StackCons(head, tail),
        index
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![StackAt {
        stack: tail,
        index: int::sub(index, 1)
    }]
}

#[k::requires(int::le(index, 0))]
#[k::equation]
fn stack_set_here(
    k::term![StackSet {
        stack: Stack::StackCons(head, tail),
        index,
        value
    }]: k::Term<WordStack>,
) -> k::Term<WordStack> {
    k::term![Stack::StackCons(value, tail)]
}

#[k::requires(int::gt(index, 0))]
#[k::equation]
fn stack_set_later(
    k::term![StackSet {
        stack: Stack::StackCons(head, tail),
        index,
        value
    }]: k::Term<WordStack>,
) -> k::Term<WordStack> {
    k::term![Stack::StackCons(
        head,
        StackSet {
            stack: tail,
            index: int::sub(index, 1),
            value
        }
    )]
}

#[k::requires(int::le(remaining, 0))]
#[k::equation]
fn stack_take_list_done(
    k::term![StackTakeList { stack, remaining }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::empty()]
}

#[k::requires(int::gt(remaining, 0))]
#[k::equation]
fn stack_take_list_empty(
    k::term![StackTakeList {
        stack: Stack::StackEmpty(),
        remaining
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::concat(
        list::item(0),
        StackTakeList {
            stack: Stack::StackEmpty(),
            remaining: int::sub(remaining, 1)
        }
    )]
}

#[k::requires(int::gt(remaining, 0))]
#[k::equation]
fn stack_take_list_item(
    k::term![StackTakeList {
        stack: Stack::StackCons(head, tail),
        remaining
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::concat(
        list::item(head),
        StackTakeList {
            stack: tail,
            remaining: int::sub(remaining, 1)
        }
    )]
}

#[k::requires(int::le(remaining, 0))]
#[k::equation]
fn stack_drop_done(
    k::term![StackDrop { stack, remaining }]: k::Term<WordStack>,
) -> k::Term<WordStack> {
    k::term![stack]
}

#[k::requires(int::gt(remaining, 0))]
#[k::equation]
fn stack_drop_empty(
    k::term![StackDrop {
        stack: Stack::StackEmpty(),
        remaining
    }]: k::Term<WordStack>,
) -> k::Term<WordStack> {
    k::term![Stack::StackEmpty()]
}

#[k::requires(int::gt(remaining, 0))]
#[k::equation]
fn stack_drop_item(
    k::term![StackDrop {
        stack: Stack::StackCons(head, tail),
        remaining
    }]: k::Term<WordStack>,
) -> k::Term<WordStack> {
    k::term![StackDrop {
        stack: tail,
        remaining: int::sub(remaining, 1)
    }]
}

#[k::requires(int::eq(StackSize(stack), 0))]
#[k::equation]
fn prepare_pop_underflow(
    k::term![PrepareStack {
        op: Operation::Pop,
        stack,
        gas
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::StackUnderflowResult()]
}

#[k::requires(int::gt(StackSize(stack), 0))]
#[k::equation]
fn prepare_pop(
    k::term![PrepareStack {
        op: Operation::Pop,
        stack,
        gas
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![ChargeFixed {
        op: Operation::Pop,
        gas,
        cost: 2
    }]
}

#[k::requires(int::lt(StackSize(stack), depth))]
#[k::equation]
fn prepare_duplicate_underflow(
    k::term![PrepareStack {
        op: Operation::Duplicate { depth },
        stack,
        gas
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::StackUnderflowResult()]
}

#[k::requires(bool::and(int::ge(StackSize(stack), depth), int::lt(StackSize(stack), 1024),))]
#[k::equation]
fn prepare_duplicate(
    k::term![PrepareStack {
        op: Operation::Duplicate { depth },
        stack,
        gas
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![ChargeFixed {
        op: Operation::Duplicate { depth },
        gas,
        cost: 3
    }]
}

#[k::requires(bool::and(int::ge(StackSize(stack), depth), int::ge(StackSize(stack), 1024),))]
#[k::equation]
fn prepare_duplicate_overflow(
    k::term![PrepareStack {
        op: Operation::Duplicate { depth },
        stack,
        gas
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::StackOverflowResult()]
}

#[k::requires(int::lt(StackSize(stack), int::add(depth, 1)))]
#[k::equation]
fn prepare_swap_underflow(
    k::term![PrepareStack {
        op: Operation::Swap { depth },
        stack,
        gas
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::StackUnderflowResult()]
}

#[k::requires(int::ge(StackSize(stack), int::add(depth, 1)))]
#[k::equation]
fn prepare_swap(
    k::term![PrepareStack {
        op: Operation::Swap { depth },
        stack,
        gas
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![ChargeFixed {
        op: Operation::Swap { depth },
        gas,
        cost: 3
    }]
}

#[k::requires(int::lt(StackSize(stack), 1024))]
#[k::equation]
fn prepare_push(
    k::term![PreparePush {
        op,
        stack,
        gas,
        cost
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![ChargeFixed { op, gas, cost }]
}

#[k::requires(int::ge(StackSize(stack), 1024))]
#[k::equation]
fn prepare_push_overflow(
    k::term![PreparePush {
        op,
        stack,
        gas,
        cost
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::StackOverflowResult()]
}

#[k::requires(int::lt(StackSize(stack), int::add(topics, 2),))]
#[k::equation]
fn prepare_log_underflow(
    k::term![PrepareLog {
        op: Operation::LogOpcode { topics },
        stack,
        gas,
        used,
        static_mode
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::StackUnderflowResult()]
}

#[k::requires(int::lt(StackSize(stack), 6))]
#[k::equation]
fn prepare_static_call_underflow(
    k::term![PrepareStaticCall {
        stack,
        accessed,
        used,
        gas
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::StackUnderflowResult()]
}

#[k::requires(int::ge(StackSize(stack), 6))]
#[k::equation]
fn prepare_static_call(
    k::term![PrepareStaticCall {
        stack,
        accessed,
        used,
        gas
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![ChargeStaticCall {
        gas,
        cost: StaticCallCost {
            accessed,
            account: StackAt { stack, index: 1 },
            used,
            argument_start: StackAt { stack, index: 2 },
            argument_width: StackAt { stack, index: 3 },
            return_start: StackAt { stack, index: 4 },
            return_width: StackAt { stack, index: 5 }
        },
        account: StackAt { stack, index: 1 }
    }]
}

#[k::requires(int::le(requested, int::sub(available, int::div(available, 64)),))]
#[k::equation]
fn static_call_gas_requested(
    k::term![StaticCallGas {
        requested,
        available
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![requested]
}

#[k::requires(int::gt(requested, int::sub(available, int::div(available, 64)),))]
#[k::equation]
fn static_call_gas_capped(
    k::term![StaticCallGas {
        requested,
        available
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::sub(available, int::div(available, 64))]
}

#[k::equation]
fn ecrec_precompile_output(
    k::term![EcrecPrecompileOutput { data }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![EcrecOutput {
        public_key: EcdsaRecover {
            hash: ReturnBytes {
                memory: data,
                start: 0,
                width: 32
            },
            recovery: BytesToInt {
                value: ReturnBytes {
                    memory: data,
                    start: 32,
                    width: 32
                },
                index: 0,
                result: 0
            },
            r: ReturnBytes {
                memory: data,
                start: 64,
                width: 32
            },
            s: ReturnBytes {
                memory: data,
                start: 96,
                width: 32
            }
        }
    }]
}

#[k::requires(int::eq(bytes::length(public_key), 0))]
#[k::equation]
fn ecrec_output_invalid(k::term![EcrecOutput { public_key }]: k::Term<Bytes>) -> k::Term<Bytes> {
    k::term![bytes::empty()]
}

#[k::requires(int::gt(bytes::length(public_key), 0))]
#[k::equation]
fn ecrec_output_valid(k::term![EcrecOutput { public_key }]: k::Term<Bytes>) -> k::Term<Bytes> {
    k::term![CopyBytes {
        memory: bytes::pad_right(bytes::empty(), 32, 0),
        destination: 12,
        source: ReturnBytes {
            memory: Keccak256Raw { value: public_key },
            start: 12,
            width: 20
        },
        source_index: 0,
        remaining: 20
    }]
}

#[k::requires(int::ge(
    StaticCallGas { requested, available },
    3000,
))]
#[k::equation]
fn resolve_ecrec_precompile_success(
    k::term![ResolveEcrecPrecompile {
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcrecPrecompileSuccess {
        remaining: int::sub(available, 3000)
    }]
}

#[k::requires(int::lt(
    StaticCallGas { requested, available },
    3000,
))]
#[k::equation]
fn resolve_ecrec_precompile_failure(
    k::term![ResolveEcrecPrecompile {
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcrecPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::equation]
fn sha256_precompile_cost(k::term![Sha256PrecompileCost { data }]: k::Term<Int>) -> k::Term<Int> {
    k::term![int::add(
        60,
        int::mul(12, int::div(int::add(bytes::length(data), 31), 32)),
    )]
}

#[k::requires(int::ge(
    StaticCallGas { requested, available },
    Sha256PrecompileCost { data },
))]
#[k::equation]
fn resolve_sha256_precompile_success(
    k::term![ResolveSha256Precompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::Sha256PrecompileSuccess {
        remaining: int::sub(available, Sha256PrecompileCost { data })
    }]
}

#[k::requires(int::lt(
    StaticCallGas { requested, available },
    Sha256PrecompileCost { data },
))]
#[k::equation]
fn resolve_sha256_precompile_failure(
    k::term![ResolveSha256Precompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::Sha256PrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::equation]
fn ripemd160_precompile_cost(
    k::term![Ripemd160PrecompileCost { data }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(
        600,
        int::mul(120, int::div(int::add(bytes::length(data), 31), 32)),
    )]
}

#[k::requires(int::ge(
    StaticCallGas { requested, available },
    Ripemd160PrecompileCost { data },
))]
#[k::equation]
fn resolve_ripemd160_precompile_success(
    k::term![ResolveRipemd160Precompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::Ripemd160PrecompileSuccess {
        remaining: int::sub(available, Ripemd160PrecompileCost { data })
    }]
}

#[k::requires(int::lt(
    StaticCallGas { requested, available },
    Ripemd160PrecompileCost { data },
))]
#[k::equation]
fn resolve_ripemd160_precompile_failure(
    k::term![ResolveRipemd160Precompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::Ripemd160PrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::equation]
fn identity_precompile_cost(
    k::term![IdentityPrecompileCost { data }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(
        15,
        int::mul(3, int::div(int::add(bytes::length(data), 31), 32)),
    )]
}

#[k::requires(int::ge(
    StaticCallGas { requested, available },
    IdentityPrecompileCost { data },
))]
#[k::equation]
fn resolve_identity_precompile_success(
    k::term![ResolveIdentityPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::IdentityPrecompileSuccess {
        remaining: int::sub(available, IdentityPrecompileCost { data })
    }]
}

#[k::requires(int::lt(
    StaticCallGas { requested, available },
    IdentityPrecompileCost { data },
))]
#[k::equation]
fn resolve_identity_precompile_failure(
    k::term![ResolveIdentityPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::IdentityPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::equation]
fn modexp_precompile_cost(k::term![ModExpPrecompileCost { data }]: k::Term<Int>) -> k::Term<Int> {
    k::term![Maximum {
        left: 200,
        right: int::div(
            int::mul(
                int::mul(
                    int::div(
                        int::add(
                            Maximum {
                                left: BytesToInt {
                                    value: ReturnBytes {
                                        memory: data,
                                        start: 0,
                                        width: 32
                                    },
                                    index: 0,
                                    result: 0
                                },
                                right: BytesToInt {
                                    value: ReturnBytes {
                                        memory: data,
                                        start: 64,
                                        width: 32
                                    },
                                    index: 0,
                                    result: 0
                                }
                            },
                            7
                        ),
                        8
                    ),
                    int::div(
                        int::add(
                            Maximum {
                                left: BytesToInt {
                                    value: ReturnBytes {
                                        memory: data,
                                        start: 0,
                                        width: 32
                                    },
                                    index: 0,
                                    result: 0
                                },
                                right: BytesToInt {
                                    value: ReturnBytes {
                                        memory: data,
                                        start: 64,
                                        width: 32
                                    },
                                    index: 0,
                                    result: 0
                                }
                            },
                            7
                        ),
                        8
                    )
                ),
                Maximum {
                    left: ModExpAdjustedExponentLength {
                        data,
                        base_length: BytesToInt {
                            value: ReturnBytes {
                                memory: data,
                                start: 0,
                                width: 32
                            },
                            index: 0,
                            result: 0
                        },
                        exponent_length: BytesToInt {
                            value: ReturnBytes {
                                memory: data,
                                start: 32,
                                width: 32
                            },
                            index: 0,
                            result: 0
                        }
                    },
                    right: 1
                }
            ),
            3
        )
    }]
}

#[k::requires(int::le(exponent_length, 32))]
#[k::equation]
fn modexp_adjusted_exponent_length_short(
    k::term![ModExpAdjustedExponentLength {
        data,
        base_length,
        exponent_length
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![ModExpExponentHeadBits {
        value: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: int::add(96, base_length),
                width: exponent_length
            },
            index: 0,
            result: 0
        }
    }]
}

#[k::requires(int::gt(exponent_length, 32))]
#[k::equation]
fn modexp_adjusted_exponent_length_long(
    k::term![ModExpAdjustedExponentLength {
        data,
        base_length,
        exponent_length
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(
        int::mul(8, int::sub(exponent_length, 32)),
        ModExpExponentHeadBits {
            value: BytesToInt {
                value: ReturnBytes {
                    memory: data,
                    start: int::add(96, base_length),
                    width: 32
                },
                index: 0,
                result: 0
            }
        }
    )]
}

#[k::requires(int::le(value, 1))]
#[k::equation]
fn modexp_exponent_head_bits_zero_or_one(
    k::term![ModExpExponentHeadBits { value }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(int::gt(value, 1))]
#[k::equation]
fn modexp_exponent_head_bits_positive(
    k::term![ModExpExponentHeadBits { value }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::log2(value)]
}

#[k::equation]
fn modexp_precompile_output(
    k::term![ModExpPrecompileOutput { data }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![ModExpOutputBody {
        body: ReturnBytes {
            memory: data,
            start: 96,
            width: Maximum {
                left: 0,
                right: int::sub(bytes::length(data), 96)
            }
        },
        base_length: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: 0,
                width: 32
            },
            index: 0,
            result: 0
        },
        exponent_length: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: 32,
                width: 32
            },
            index: 0,
            result: 0
        },
        modulus_length: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: 64,
                width: 32
            },
            index: 0,
            result: 0
        }
    }]
}

#[k::equation]
fn modexp_output_body_empty(
    k::term![ModExpOutputBody {
        body,
        base_length,
        exponent_length,
        modulus_length: 0
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![bytes::empty()]
}

#[k::requires(int::gt(modulus_length, 0))]
#[k::equation]
fn modexp_output_body_nonempty(
    k::term![ModExpOutputBody {
        body,
        base_length,
        exponent_length,
        modulus_length
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![ModExpOutputExponent {
        body: ReturnBytes {
            memory: body,
            start: base_length,
            width: Maximum {
                left: 0,
                right: int::sub(bytes::length(body), base_length)
            }
        },
        base: BytesToInt {
            value: ReturnBytes {
                memory: body,
                start: 0,
                width: base_length
            },
            index: 0,
            result: 0
        },
        exponent_length,
        modulus_length
    }]
}

#[k::equation]
fn modexp_output_exponent(
    k::term![ModExpOutputExponent {
        body,
        base,
        exponent_length,
        modulus_length
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![WriteMemoryWord {
        memory: bytes::pad_right(bytes::empty(), modulus_length, 0),
        index: 0,
        remaining: modulus_length,
        value: ModExpPower {
            base,
            exponent: BytesToInt {
                value: ReturnBytes {
                    memory: body,
                    start: 0,
                    width: exponent_length
                },
                index: 0,
                result: 0
            },
            modulus: BytesToInt {
                value: ReturnBytes {
                    memory: body,
                    start: exponent_length,
                    width: modulus_length
                },
                index: 0,
                result: 0
            }
        }
    }]
}

#[k::requires(int::eq(modulus, 0))]
#[k::equation]
fn modexp_power_zero_modulus(
    k::term![ModExpPower {
        base,
        exponent,
        modulus
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![0]
}

#[k::requires(int::gt(modulus, 0))]
#[k::equation]
fn modexp_power_nonzero_modulus(
    k::term![ModExpPower {
        base,
        exponent,
        modulus
    }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::pow_mod(base, exponent, modulus)]
}

#[k::requires(int::ge(
    StaticCallGas { requested, available },
    ModExpPrecompileCost { data },
))]
#[k::equation]
fn resolve_modexp_precompile_success(
    k::term![ResolveModExpPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::ModExpPrecompileSuccess {
        remaining: int::sub(available, ModExpPrecompileCost { data })
    }]
}

#[k::requires(int::lt(
    StaticCallGas { requested, available },
    ModExpPrecompileCost { data },
))]
#[k::equation]
fn resolve_modexp_precompile_failure(
    k::term![ResolveModExpPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::ModExpPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::equation]
fn ecadd_first_point(k::term![EcAddFirstPoint { data }]: k::Term<G1Point>) -> k::Term<G1Point> {
    k::term![Bn128Point::Point {
        x: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: 0,
                width: 32
            },
            index: 0,
            result: 0
        },
        y: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: 32,
                width: 32
            },
            index: 0,
            result: 0
        }
    }]
}

#[k::equation]
fn ecadd_second_point(k::term![EcAddSecondPoint { data }]: k::Term<G1Point>) -> k::Term<G1Point> {
    k::term![Bn128Point::Point {
        x: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: 64,
                width: 32
            },
            index: 0,
            result: 0
        },
        y: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: 96,
                width: 32
            },
            index: 0,
            result: 0
        }
    }]
}

#[k::equation]
fn bn128_point_bytes(
    k::term![Bn128PointBytes {
        point: Bn128Point::Point { x, y }
    }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![WriteMemoryWord {
        memory: WriteMemoryWord {
            memory: bytes::pad_right(bytes::empty(), 64, 0),
            index: 0,
            remaining: 32,
            value: x
        },
        index: 32,
        remaining: 32,
        value: y
    }]
}

#[k::equation]
fn ecadd_precompile_output(
    k::term![EcAddPrecompileOutput { data }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![Bn128PointBytes {
        point: Bn128Add {
            left: EcAddFirstPoint { data },
            right: EcAddSecondPoint { data }
        }
    }]
}

#[k::requires(bool::and(
    int::ge(StaticCallGas { requested, available }, 150),
    bool::and(
        Bn128PointValid {
            point: EcAddFirstPoint { data }
        },
        Bn128PointValid {
            point: EcAddSecondPoint { data }
        },
    ),
))]
#[k::equation]
fn resolve_ecadd_precompile_success(
    k::term![ResolveEcAddPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcAddPrecompileSuccess {
        remaining: int::sub(available, 150)
    }]
}

#[k::requires(int::lt(StaticCallGas { requested, available }, 150))]
#[k::equation]
fn resolve_ecadd_precompile_out_of_gas(
    k::term![ResolveEcAddPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcAddPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::requires(bool::and(
    int::ge(StaticCallGas { requested, available }, 150),
    bool::not(Bn128PointValid {
        point: EcAddFirstPoint { data }
    }),
))]
#[k::equation]
fn resolve_ecadd_precompile_invalid_first_point(
    k::term![ResolveEcAddPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcAddPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::requires(bool::and(
    int::ge(StaticCallGas { requested, available }, 150),
    bool::and(
        Bn128PointValid {
            point: EcAddFirstPoint { data }
        },
        bool::not(Bn128PointValid {
            point: EcAddSecondPoint { data }
        }),
    ),
))]
#[k::equation]
fn resolve_ecadd_precompile_invalid_second_point(
    k::term![ResolveEcAddPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcAddPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::equation]
fn ecmul_point(k::term![EcMulPoint { data }]: k::Term<G1Point>) -> k::Term<G1Point> {
    k::term![Bn128Point::Point {
        x: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: 0,
                width: 32
            },
            index: 0,
            result: 0
        },
        y: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: 32,
                width: 32
            },
            index: 0,
            result: 0
        }
    }]
}

#[k::equation]
fn ecmul_scalar(k::term![EcMulScalar { data }]: k::Term<Int>) -> k::Term<Int> {
    k::term![BytesToInt {
        value: ReturnBytes {
            memory: data,
            start: 64,
            width: 32
        },
        index: 0,
        result: 0
    }]
}

#[k::equation]
fn ecmul_precompile_output(
    k::term![EcMulPrecompileOutput { data }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![Bn128PointBytes {
        point: Bn128Mul {
            point: EcMulPoint { data },
            scalar: EcMulScalar { data }
        }
    }]
}

#[k::requires(bool::and(
    int::ge(StaticCallGas { requested, available }, 6000),
    Bn128PointValid {
        point: EcMulPoint { data }
    },
))]
#[k::equation]
fn resolve_ecmul_precompile_success(
    k::term![ResolveEcMulPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcMulPrecompileSuccess {
        remaining: int::sub(available, 6000)
    }]
}

#[k::requires(int::lt(StaticCallGas { requested, available }, 6000))]
#[k::equation]
fn resolve_ecmul_precompile_out_of_gas(
    k::term![ResolveEcMulPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcMulPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::requires(bool::and(
    int::ge(StaticCallGas { requested, available }, 6000),
    bool::not(Bn128PointValid {
        point: EcMulPoint { data }
    }),
))]
#[k::equation]
fn resolve_ecmul_precompile_invalid_point(
    k::term![ResolveEcMulPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcMulPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::equation]
fn ecpairing_precompile_cost(
    k::term![EcPairingPrecompileCost { data }]: k::Term<Int>,
) -> k::Term<Int> {
    k::term![int::add(
        45000,
        int::mul(34000, int::div(bytes::length(data), 192))
    )]
}

#[k::equation]
fn ecpairing_g1_point(
    k::term![EcPairingG1Point { data, index }]: k::Term<G1Point>,
) -> k::Term<G1Point> {
    k::term![Bn128Point::Point {
        x: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: index,
                width: 32
            },
            index: 0,
            result: 0
        },
        y: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: int::add(index, 32),
                width: 32
            },
            index: 0,
            result: 0
        }
    }]
}

#[k::equation]
fn ecpairing_g2_point(
    k::term![EcPairingG2Point { data, index }]: k::Term<G2Point>,
) -> k::Term<G2Point> {
    k::term![Bn128G2Point::G2 {
        x_real: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: int::add(index, 96),
                width: 32
            },
            index: 0,
            result: 0
        },
        x_imaginary: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: int::add(index, 64),
                width: 32
            },
            index: 0,
            result: 0
        },
        y_real: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: int::add(index, 160),
                width: 32
            },
            index: 0,
            result: 0
        },
        y_imaginary: BytesToInt {
            value: ReturnBytes {
                memory: data,
                start: int::add(index, 128),
                width: 32
            },
            index: 0,
            result: 0
        }
    }]
}

#[k::requires(int::eq(index, length))]
#[k::equation]
fn ecpairing_g1_points_done(
    k::term![EcPairingG1Points {
        data,
        index,
        length
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::empty()]
}

#[k::requires(int::lt(index, length))]
#[k::equation]
fn ecpairing_g1_points_next(
    k::term![EcPairingG1Points {
        data,
        index,
        length
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::concat(
        list::item(EcPairingG1Point { data, index }),
        EcPairingG1Points {
            data,
            index: int::add(index, 192),
            length
        }
    )]
}

#[k::requires(int::eq(index, length))]
#[k::equation]
fn ecpairing_g2_points_done(
    k::term![EcPairingG2Points {
        data,
        index,
        length
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::empty()]
}

#[k::requires(int::lt(index, length))]
#[k::equation]
fn ecpairing_g2_points_next(
    k::term![EcPairingG2Points {
        data,
        index,
        length
    }]: k::Term<List>,
) -> k::Term<List> {
    k::term![list::concat(
        list::item(EcPairingG2Point { data, index }),
        EcPairingG2Points {
            data,
            index: int::add(index, 192),
            length
        }
    )]
}

#[k::requires(int::eq(index, length))]
#[k::equation]
fn ecpairing_points_valid_done(
    k::term![EcPairingPointsValid {
        data,
        index,
        length
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![true]
}

#[k::requires(int::lt(index, length))]
#[k::equation]
fn ecpairing_points_valid_next(
    k::term![EcPairingPointsValid {
        data,
        index,
        length
    }]: k::Term<Bool>,
) -> k::Term<Bool> {
    k::term![bool::and(
        Bn128PointValid {
            point: EcPairingG1Point { data, index }
        },
        bool::and(
            Bn128G2PointValid {
                point: EcPairingG2Point { data, index }
            },
            EcPairingPointsValid {
                data,
                index: int::add(index, 192),
                length
            }
        )
    )]
}

#[k::equation]
fn ecpairing_precompile_output(
    k::term![EcPairingPrecompileOutput { data }]: k::Term<Bytes>,
) -> k::Term<Bytes> {
    k::term![WriteMemoryWord {
        memory: bytes::pad_right(bytes::empty(), 32, 0),
        index: 0,
        remaining: 32,
        value: BoolToWord(Bn128Ate {
            g1_points: EcPairingG1Points {
                data,
                index: 0,
                length: bytes::length(data)
            },
            g2_points: EcPairingG2Points {
                data,
                index: 0,
                length: bytes::length(data)
            }
        })
    }]
}

#[k::requires(bool::and(
    int::ge(
        StaticCallGas { requested, available },
        EcPairingPrecompileCost { data }
    ),
    bool::and(
        int::eq(int::modulo(bytes::length(data), 192), 0),
        EcPairingPointsValid {
            data,
            index: 0,
            length: bytes::length(data)
        },
    ),
))]
#[k::equation]
fn resolve_ecpairing_precompile_success(
    k::term![ResolveEcPairingPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcPairingPrecompileSuccess {
        remaining: int::sub(available, EcPairingPrecompileCost { data })
    }]
}

#[k::requires(int::lt(
    StaticCallGas { requested, available },
    EcPairingPrecompileCost { data }
))]
#[k::equation]
fn resolve_ecpairing_precompile_out_of_gas(
    k::term![ResolveEcPairingPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcPairingPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::requires(bool::and(
    int::ge(
        StaticCallGas { requested, available },
        EcPairingPrecompileCost { data }
    ),
    int::ne(int::modulo(bytes::length(data), 192), 0),
))]
#[k::equation]
fn resolve_ecpairing_precompile_malformed_length(
    k::term![ResolveEcPairingPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcPairingPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::requires(bool::and(
    int::ge(
        StaticCallGas { requested, available },
        EcPairingPrecompileCost { data }
    ),
    bool::and(
        int::eq(int::modulo(bytes::length(data), 192), 0),
        bool::not(EcPairingPointsValid {
            data,
            index: 0,
            length: bytes::length(data)
        }),
    ),
))]
#[k::equation]
fn resolve_ecpairing_precompile_invalid_point(
    k::term![ResolveEcPairingPrecompile {
        data,
        requested,
        available
    }]: k::Term<PrecompileStep>,
) -> k::Term<PrecompileStep> {
    k::term![PrecompileResult::EcPairingPrecompileFailure {
        remaining: int::sub(
            available,
            StaticCallGas {
                requested,
                available
            }
        )
    }]
}

#[k::requires(int::le(left, right))]
#[k::equation]
fn minimum_left(k::term![Minimum { left, right }]: k::Term<Int>) -> k::Term<Int> {
    k::term![left]
}

#[k::requires(int::gt(left, right))]
#[k::equation]
fn minimum_right(k::term![Minimum { left, right }]: k::Term<Int>) -> k::Term<Int> {
    k::term![right]
}

#[k::requires(int::ge(left, right))]
#[k::equation]
fn maximum_left(k::term![Maximum { left, right }]: k::Term<Int>) -> k::Term<Int> {
    k::term![left]
}

#[k::requires(int::lt(left, right))]
#[k::equation]
fn maximum_right(k::term![Maximum { left, right }]: k::Term<Int>) -> k::Term<Int> {
    k::term![right]
}

#[k::requires(int::ge(StackSize(stack), int::add(topics, 2),))]
#[k::equation]
fn prepare_log_static(
    k::term![PrepareLog {
        op: Operation::LogOpcode { topics },
        stack,
        gas,
        used,
        static_mode: true
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::StaticViolationResult()]
}

#[k::requires(int::ge(StackSize(stack), int::add(topics, 2),))]
#[k::equation]
fn prepare_log_allowed(
    k::term![PrepareLog {
        op: Operation::LogOpcode { topics },
        stack,
        gas,
        used,
        static_mode: false
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![ChargeFixed {
        op: Operation::LogOpcode { topics },
        gas,
        cost: int::add(
            MemoryExpansionCost {
                used,
                start: StackAt { stack, index: 0 },
                width: StackAt { stack, index: 1 }
            },
            int::add(
                375,
                int::add(
                    int::mul(8, StackAt { stack, index: 1 }),
                    int::mul(375, topics),
                ),
            ),
        )
    }]
}

#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_fixed(k::term![ChargeFixed { op, gas, cost }]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op,
        remaining: int::sub(gas, cost)
    }]
}

#[k::requires(int::lt(gas, cost))]
#[k::equation]
fn charge_fixed_fails(
    k::term![ChargeFixed { op, gas, cost }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::InsufficientGas()]
}

#[k::priority(40)]
#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_static_call_ecrec(
    k::term![ChargeStaticCall {
        gas,
        cost,
        account: 1
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughEcrecPrecompileGas {
        remaining: int::sub(gas, cost)
    }]
}

#[k::priority(40)]
#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_static_call_sha256(
    k::term![ChargeStaticCall {
        gas,
        cost,
        account: 2
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughSha256PrecompileGas {
        remaining: int::sub(gas, cost)
    }]
}

#[k::priority(40)]
#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_static_call_ripemd160(
    k::term![ChargeStaticCall {
        gas,
        cost,
        account: 3
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughRipemd160PrecompileGas {
        remaining: int::sub(gas, cost)
    }]
}

#[k::priority(40)]
#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_static_call_identity(
    k::term![ChargeStaticCall {
        gas,
        cost,
        account: 4
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughIdentityPrecompileGas {
        remaining: int::sub(gas, cost)
    }]
}

#[k::priority(40)]
#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_static_call_modexp(
    k::term![ChargeStaticCall {
        gas,
        cost,
        account: 5
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughModExpPrecompileGas {
        remaining: int::sub(gas, cost)
    }]
}

#[k::priority(40)]
#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_static_call_ecadd(
    k::term![ChargeStaticCall {
        gas,
        cost,
        account: 6
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughEcAddPrecompileGas {
        remaining: int::sub(gas, cost)
    }]
}

#[k::priority(40)]
#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_static_call_ecmul(
    k::term![ChargeStaticCall {
        gas,
        cost,
        account: 7
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughEcMulPrecompileGas {
        remaining: int::sub(gas, cost)
    }]
}

#[k::priority(40)]
#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_static_call_ecpairing(
    k::term![ChargeStaticCall {
        gas,
        cost,
        account: 8
    }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughEcPairingPrecompileGas {
        remaining: int::sub(gas, cost)
    }]
}

#[k::priority(50)]
#[k::requires(int::ge(gas, cost))]
#[k::equation]
fn charge_static_call(
    k::term![ChargeStaticCall { gas, cost, account }]: k::Term<GasStep>,
) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::StaticCall,
        remaining: int::sub(gas, cost)
    }]
}

#[k::requires(int::lt(gas, cost))]
#[k::equation]
fn charge_static_call_fails(
    k::term![ChargeStaticCall { gas, cost, account }]: k::Term<GasStep>,
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

#[k::equation]
fn charge_stop(k::term![Charge(Operation::Stop, gas)]: k::Term<GasStep>) -> k::Term<GasStep> {
    k::term![GasResult::EnoughGas {
        op: Operation::Stop,
        remaining: gas
    }]
}

#[k::cell]
pub struct CallState {
    #[k::cell(name = "program")]
    pub program: Bytes,
    #[k::cell(name = "jumpDests")]
    pub jump_dests: Bytes,
    #[k::cell(name = "id")]
    pub address: Int,
    #[k::cell(name = "caller")]
    pub caller: Int,
    #[k::cell(name = "callData")]
    pub call_data: Bytes,
    #[k::cell(name = "callValue")]
    pub call_value: Int,
    #[k::cell(name = "wordStack")]
    pub word_stack: WordStack,
    #[k::cell(name = "localMem")]
    pub local_mem: Bytes,
    #[k::cell(name = "pc")]
    pub pc: Int,
    #[k::cell(name = "gas")]
    pub gas: Int,
    #[k::cell(name = "memoryUsed")]
    pub memory_used: Int,
    #[k::cell(name = "callGas")]
    pub call_gas: Int,
    #[k::cell(name = "static")]
    pub static_mode: Bool,
    #[k::cell(name = "callDepth")]
    pub call_depth: Int,
    #[k::cell(name = "codeAddr")]
    pub code_address: Int,
}

#[k::cell]
pub struct Substate {
    #[k::cell(name = "selfDestruct")]
    pub self_destruct: Set<Int>,
    #[k::cell(name = "log")]
    pub logs: List<LogEntry>,
    #[k::cell(name = "refund")]
    pub refund: Int,
    #[k::cell(name = "accessedAccounts")]
    pub accessed_accounts: Set<Int>,
    #[k::cell(name = "accessedStorage")]
    pub accessed_storage: Map<Int, Set<Int>>,
    #[k::cell(name = "createdAccounts")]
    pub created_accounts: Set<Int>,
}

#[k::cell]
pub struct Account {
    #[k::cell(name = "acctID")]
    pub account_id: Int,
    #[k::cell(name = "balance")]
    pub balance: Int,
    #[k::cell(name = "code")]
    pub code: Bytes,
    #[k::cell(name = "nonce")]
    pub nonce: Int,
    #[k::cell(name = "storage")]
    pub storage: Map<Int, Int>,
    #[k::cell(name = "origStorage")]
    pub original_storage: Map<Int, Int>,
}

#[k::cell]
pub struct Accounts {
    #[k::cell(name = "account", multiplicity = "*", cell_type = "Map", nested)]
    pub account: Account,
}

#[k::configuration]
pub struct Machine {
    #[k::cell(name = "k")]
    pub k: KSequence,
    #[k::cell(name = "output")]
    pub output: Bytes,
    #[k::cell(name = "statusCode")]
    pub status_code: StatusCode,
    #[k::cell(name = "callStack")]
    pub call_stack: List,
    #[k::cell(name = "interimStates")]
    pub interim_states: List,
    #[k::cell(name = "touchedAccounts")]
    pub touched_accounts: Set<Int>,
    #[k::cell(name = "callState", nested)]
    pub call_state: CallState,
    #[k::cell(name = "substate", nested)]
    pub substate: Substate,
    #[k::cell(name = "origin")]
    pub origin: Int,
    #[k::cell(name = "gasPrice")]
    pub gas_price: Int,
    #[k::cell(name = "accounts", nested)]
    pub accounts: Accounts,
    #[k::cell(name = "blockhashes")]
    pub block_hashes: List<Int>,
    #[k::cell(name = "coinbase")]
    pub coinbase: Int,
    #[k::cell(name = "timestamp")]
    pub timestamp: Int,
    #[k::cell(name = "number")]
    pub number: Int,
    #[k::cell(name = "mixHash")]
    pub prev_randao: Int,
    #[k::cell(name = "gasLimit")]
    pub gas_limit: Int,
    #[k::cell(name = "chainID")]
    pub chain_id: Int,
    #[k::cell(name = "baseFee")]
    pub base_fee: Int,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] command: KSequence,
        #[k::config_var(name = "PROGRAM")] program: Bytes,
        #[k::config_var(name = "JUMPDESTS")] jump_dests: Bytes,
        #[k::config_var(name = "ADDRESS")] address: Int,
        #[k::config_var(name = "ACCOUNTID")] account_id: Int,
        #[k::config_var(name = "BALANCE")] balance: Int,
        #[k::config_var(name = "CODE")] code: Bytes,
        #[k::config_var(name = "NONCE")] nonce: Int,
        #[k::config_var(name = "ORIGIN")] origin: Int,
        #[k::config_var(name = "CALLER")] caller: Int,
        #[k::config_var(name = "CALLVALUE")] call_value: Int,
        #[k::config_var(name = "CALLDATA")] call_data: Bytes,
        #[k::config_var(name = "GASPRICE")] gas_price: Int,
        #[k::config_var(name = "RETURNDATA")] output: Bytes,
        #[k::config_var(name = "LOCALMEM")] local_mem: Bytes,
        #[k::config_var(name = "MEMORYUSED")] memory_used: Int,
        #[k::config_var(name = "CALLGAS")] call_gas: Int,
        #[k::config_var(name = "CALLDEPTH")] call_depth: Int,
        #[k::config_var(name = "CODEADDRESS")] code_address: Int,
        #[k::config_var(name = "CALLSTACK")] call_stack: List,
        #[k::config_var(name = "INTERIMSTATES")] interim_states: List,
        #[k::config_var(name = "TOUCHEDACCOUNTS")] touched_accounts: Set<Int>,
        #[k::config_var(name = "STORAGE")] storage: Map<Int, Int>,
        #[k::config_var(name = "ORIGSTORAGE")] original_storage: Map<Int, Int>,
        #[k::config_var(name = "ACCESSEDSTORAGE")] accessed_storage: Map<Int, Set<Int>>,
        #[k::config_var(name = "ACCESSEDACCOUNTS")] accessed_accounts: Set<Int>,
        #[k::config_var(name = "LOGS")] logs: List<LogEntry>,
        #[k::config_var(name = "REFUND")] refund: Int,
        #[k::config_var(name = "SELFDESTRUCT")] self_destruct: Set<Int>,
        #[k::config_var(name = "CREATEDACCOUNTS")] created_accounts: Set<Int>,
        #[k::config_var(name = "STATIC")] static_mode: Bool,
        #[k::config_var(name = "BLOCKHASHES")] block_hashes: List<Int>,
        #[k::config_var(name = "COINBASE")] coinbase: Int,
        #[k::config_var(name = "TIMESTAMP")] timestamp: Int,
        #[k::config_var(name = "NUMBER")] number: Int,
        #[k::config_var(name = "PREVRANDAO")] prev_randao: Int,
        #[k::config_var(name = "GASLIMIT")] gas_limit: Int,
        #[k::config_var(name = "CHAINID")] chain_id: Int,
        #[k::config_var(name = "BASEFEE")] base_fee: Int,
        #[k::config_var(name = "STACK")] word_stack: WordStack,
        #[k::config_var(name = "PC")] pc: Int,
        #[k::config_var(name = "GAS")] gas: Int,
        #[k::config_var(name = "STATUS")] status_code: StatusCode,
    ) -> Self {
        Self {
            k: k::k![command],
            output,
            status_code,
            call_stack,
            interim_states,
            touched_accounts,
            call_state: CallState {
                program,
                jump_dests,
                address,
                caller,
                call_data,
                call_value,
                word_stack,
                local_mem,
                pc,
                gas,
                memory_used,
                call_gas,
                static_mode,
                call_depth,
                code_address,
            },
            substate: Substate {
                self_destruct,
                logs,
                refund,
                accessed_accounts,
                accessed_storage,
                created_accounts,
            },
            origin,
            gas_price,
            accounts: Accounts {
                account: Account {
                    account_id,
                    balance,
                    code,
                    nonce,
                    storage,
                    original_storage,
                },
            },
            block_hashes,
            coinbase,
            timestamp,
            number,
            prev_randao,
            gas_limit,
            chain_id,
            base_fee,
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
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::Push { width, value }, stack, gas, cost: 3 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where width: Int, value: Int, stack: WordStack, gas: Int;

    begin_push_zero: {
        k: [Operation::PushZero, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::PushZero, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_pop: {
        k: [Operation::Pop, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PrepareStack { op: Operation::Pop, stack, gas }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_duplicate: {
        k: [Operation::Duplicate { depth }, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PrepareStack { op: Operation::Duplicate { depth }, stack, gas }, ..],
        word_stack: stack,
        gas: gas,
    }
    where depth: Int, stack: WordStack, gas: Int;

    begin_swap: {
        k: [Operation::Swap { depth }, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PrepareStack { op: Operation::Swap { depth }, stack, gas }, ..],
        word_stack: stack,
        gas: gas,
    }
    where depth: Int, stack: WordStack, gas: Int;

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

    begin_exponent: {
        k: [Operation::Exponent, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::Exponent, gas, cost: crate::ExpCost(w1) }, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_sign_extend: {
        k: [Operation::SignExtend, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::SignExtend, gas, cost: 5 }, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

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

    begin_bit_and: {
        k: [Operation::BitAnd, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::BitAnd, gas, cost: 3 }, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_bit_or: {
        k: [Operation::BitOr, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::BitOr, gas, cost: 3 }, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_bit_xor: {
        k: [Operation::BitXor, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::BitXor, gas, cost: 3 }, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_bit_not: {
        k: [Operation::BitNot, ..],
        word_stack: Stack::StackCons(w0, rest),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::BitNot, gas, cost: 3 }, ..],
        word_stack: Stack::StackCons(w0, rest),
        gas: gas,
    }
    where w0: Int, rest: WordStack, gas: Int;

    begin_byte: {
        k: [Operation::Byte, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::Byte, gas, cost: 3 }, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_shift_left: {
        k: [Operation::ShiftLeft, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::ShiftLeft, gas, cost: 3 }, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_shift_right: {
        k: [Operation::ShiftRight, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::ShiftRight, gas, cost: 3 }, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_signed_shift_right: {
        k: [Operation::SignedShiftRight, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::SignedShiftRight, gas, cost: 3 }, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        gas: gas,
    }
    where w0: Int, w1: Int, rest: WordStack, gas: Int;

    begin_address: {
        k: [Operation::Address, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::Address, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_balance: {
        k: [Operation::AccountBalance, ..],
        word_stack: Stack::StackCons(account, rest),
        accessed_accounts: accessed,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::AccountBalance, gas, cost: crate::AccountAccessCost { accessed, account } }, ..],
        word_stack: Stack::StackCons(account, rest),
        accessed_accounts: accessed,
        gas: gas,
    }
    where account: Int, rest: WordStack, accessed: Set, gas: Int;

    begin_origin: {
        k: [Operation::TxOrigin, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::TxOrigin, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_caller: {
        k: [Operation::MsgCaller, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::MsgCaller, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_call_value: {
        k: [Operation::MsgCallValue, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::MsgCallValue, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_call_data_load: {
        k: [Operation::CallDataLoad, ..],
        word_stack: Stack::StackCons(index, rest),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::CallDataLoad, gas, cost: 3 }, ..],
        word_stack: Stack::StackCons(index, rest),
        gas: gas,
    }
    where index: Int, rest: WordStack, gas: Int;

    begin_call_data_size: {
        k: [Operation::CallDataSize, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::CallDataSize, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_call_data_copy: {
        k: [Operation::CallDataCopy, ..],
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        memory_used: used,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::CallDataCopy, gas, cost: crate::CopyGasCost { used, start: destination, width } }, ..],
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        memory_used: used,
        gas: gas,
    }
    where destination: Int, source_index: Int, width: Int, rest: WordStack, used: Int, gas: Int;

    begin_code_size: {
        k: [Operation::CodeSize, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::CodeSize, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_code_copy: {
        k: [Operation::CodeCopy, ..],
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        memory_used: used,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::CodeCopy, gas, cost: crate::CopyGasCost { used, start: destination, width } }, ..],
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        memory_used: used,
        gas: gas,
    }
    where destination: Int, source_index: Int, width: Int, rest: WordStack, used: Int, gas: Int;

    begin_gas_price: {
        k: [Operation::TxGasPrice, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::TxGasPrice, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_external_code_size: {
        k: [Operation::ExternalCodeSize, ..],
        word_stack: Stack::StackCons(account, rest),
        accessed_accounts: accessed,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::ExternalCodeSize, gas, cost: crate::AccountAccessCost { accessed, account } }, ..],
        word_stack: Stack::StackCons(account, rest),
        accessed_accounts: accessed,
        gas: gas,
    }
    where account: Int, rest: WordStack, accessed: Set, gas: Int;

    begin_external_code_copy: {
        k: [Operation::ExternalCodeCopy, ..],
        word_stack: Stack::StackCons(account, Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest)))),
        memory_used: used,
        accessed_accounts: accessed,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::ExternalCodeCopy, gas, cost: crate::ExternalCopyGasCost { accessed, account, used, start: destination, width } }, ..],
        word_stack: Stack::StackCons(account, Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest)))),
        memory_used: used,
        accessed_accounts: accessed,
        gas: gas,
    }
    where account: Int, destination: Int, source_index: Int, width: Int, rest: WordStack, used: Int, accessed: Set, gas: Int;

    begin_return_data_size: {
        k: [Operation::ReturnDataSize, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::ReturnDataSize, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_return_data_copy: {
        k: [Operation::ReturnDataCopy, ..],
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        memory_used: used,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::ReturnDataCopy, gas, cost: crate::CopyGasCost { used, start: destination, width } }, ..],
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        memory_used: used,
        gas: gas,
    }
    where destination: Int, source_index: Int, width: Int, rest: WordStack, used: Int, gas: Int;

    begin_external_code_hash: {
        k: [Operation::ExternalCodeHash, ..],
        word_stack: Stack::StackCons(account, rest),
        accessed_accounts: accessed,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::ExternalCodeHash, gas, cost: crate::AccountAccessCost { accessed, account } }, ..],
        word_stack: Stack::StackCons(account, rest),
        accessed_accounts: accessed,
        gas: gas,
    }
    where account: Int, rest: WordStack, accessed: Set, gas: Int;

    begin_block_hash: {
        k: [Operation::BlockHash, ..],
        word_stack: Stack::StackCons(requested, rest),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::BlockHash, gas, cost: 20 }, ..],
        word_stack: Stack::StackCons(requested, rest),
        gas: gas,
    }
    where requested: Int, rest: WordStack, gas: Int;

    begin_self_balance: {
        k: [Operation::SelfBalance, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::SelfBalance, stack, gas, cost: 5 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_coinbase: {
        k: [Operation::BlockCoinbase, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::BlockCoinbase, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_timestamp: {
        k: [Operation::BlockTimestamp, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::BlockTimestamp, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_number: {
        k: [Operation::BlockNumber, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::BlockNumber, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_prev_randao: {
        k: [Operation::PrevRandao, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::PrevRandao, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_gas_limit: {
        k: [Operation::BlockGasLimit, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::BlockGasLimit, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_chain_id: {
        k: [Operation::NetworkChainId, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::NetworkChainId, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_base_fee: {
        k: [Operation::BlockBaseFee, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::BlockBaseFee, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_memory_load: {
        k: [Operation::MemoryLoad, ..],
        word_stack: Stack::StackCons(index, rest),
        memory_used: used,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::MemoryLoad, gas, cost: int::add(3, crate::MemoryExpansionCost { used, start: index, width: 32 }) }, ..],
        word_stack: Stack::StackCons(index, rest),
        memory_used: used,
        gas: gas,
    }
    where index: Int, rest: WordStack, used: Int, gas: Int;

    begin_memory_store: {
        k: [Operation::MemoryStore, ..],
        word_stack: Stack::StackCons(index, Stack::StackCons(value, rest)),
        memory_used: used,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::MemoryStore, gas, cost: int::add(3, crate::MemoryExpansionCost { used, start: index, width: 32 }) }, ..],
        word_stack: Stack::StackCons(index, Stack::StackCons(value, rest)),
        memory_used: used,
        gas: gas,
    }
    where index: Int, value: Int, rest: WordStack, used: Int, gas: Int;

    begin_memory_store8: {
        k: [Operation::MemoryStore8, ..],
        word_stack: Stack::StackCons(index, Stack::StackCons(value, rest)),
        memory_used: used,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::MemoryStore8, gas, cost: int::add(3, crate::MemoryExpansionCost { used, start: index, width: 1 }) }, ..],
        word_stack: Stack::StackCons(index, Stack::StackCons(value, rest)),
        memory_used: used,
        gas: gas,
    }
    where index: Int, value: Int, rest: WordStack, used: Int, gas: Int;

    begin_sha3: {
        k: [Operation::Sha3, ..],
        word_stack: Stack::StackCons(start, Stack::StackCons(width, rest)),
        memory_used: used,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::Sha3, gas, cost: int::add(crate::MemoryExpansionCost { used, start, width }, int::add(30, int::mul(6, int::div(int::add(width, 31), 32)))) }, ..],
        word_stack: Stack::StackCons(start, Stack::StackCons(width, rest)),
        memory_used: used,
        gas: gas,
    }
    where start: Int, width: Int, rest: WordStack, used: Int, gas: Int;

    #[k::requires(int::eq(current_account, account_id))]
    begin_storage_load: {
        k: [Operation::StorageLoad, ..],
        address: current_account,
        account_id: account_id,
        storage: storage,
        accessed_storage: accessed,
        word_stack: Stack::StackCons(index, rest),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::StorageLoad, gas, cost: crate::StorageLoadCost { warm: crate::StorageWarm { accessed, account: current_account, index } } }, ..],
        address: current_account,
        account_id: account_id,
        storage: storage,
        accessed_storage: accessed,
        word_stack: Stack::StackCons(index, rest),
        gas: gas,
    }
    where current_account: Int, account_id: Int, storage: Map, accessed: Map, index: Int, rest: WordStack, gas: Int;

    #[k::requires(int::eq(current_account, account_id))]
    begin_storage_store: {
        k: [Operation::StorageStore, ..],
        address: current_account,
        account_id: account_id,
        storage: storage,
        original_storage: original_storage,
        accessed_storage: accessed,
        static_mode: static_mode,
        word_stack: Stack::StackCons(index, Stack::StackCons(new, rest)),
        gas: gas,
    } => {
        k: [crate::PrepareStorageStore { gas, original: crate::StorageValue { storage: original_storage, index }, current: crate::StorageValue { storage, index }, new, warm: crate::StorageWarm { accessed, account: current_account, index }, static_mode }, ..],
        address: current_account,
        account_id: account_id,
        storage: storage,
        original_storage: original_storage,
        accessed_storage: accessed,
        static_mode: static_mode,
        word_stack: Stack::StackCons(index, Stack::StackCons(new, rest)),
        gas: gas,
    }
    where current_account: Int, account_id: Int, storage: Map, original_storage: Map, accessed: Map, static_mode: Bool, index: Int, new: Int, rest: WordStack, gas: Int;

    begin_log: {
        k: [Operation::LogOpcode { topics }, ..],
        word_stack: stack,
        memory_used: used,
        static_mode: static_mode,
        gas: gas,
    } => {
        k: [crate::PrepareLog { op: Operation::LogOpcode { topics }, stack, gas, used, static_mode }, ..],
        word_stack: stack,
        memory_used: used,
        static_mode: static_mode,
        gas: gas,
    }
    where topics: Int, stack: WordStack, used: Int, static_mode: Bool, gas: Int;

    begin_memory_size: {
        k: [Operation::MemorySize, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::MemorySize, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_gas_remaining: {
        k: [Operation::GasRemaining, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::GasRemaining, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_pc: {
        k: [Operation::ProgramCounter, ..],
        word_stack: stack,
        gas: gas,
    } => {
        k: [crate::PreparePush { op: Operation::ProgramCounter, stack, gas, cost: 2 }, ..],
        word_stack: stack,
        gas: gas,
    }
    where stack: WordStack, gas: Int;

    begin_jump: {
        k: [Operation::Jump, ..],
        word_stack: Stack::StackCons(destination, rest),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::Jump, gas, cost: 8 }, ..],
        word_stack: Stack::StackCons(destination, rest),
        gas: gas,
    }
    where destination: Int, rest: WordStack, gas: Int;

    begin_jump_if: {
        k: [Operation::JumpIf, ..],
        word_stack: Stack::StackCons(destination, Stack::StackCons(condition, rest)),
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::JumpIf, gas, cost: 10 }, ..],
        word_stack: Stack::StackCons(destination, Stack::StackCons(condition, rest)),
        gas: gas,
    }
    where destination: Int, condition: Int, rest: WordStack, gas: Int;

    begin_jump_dest: {
        k: [Operation::JumpDest, ..],
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::JumpDest, gas, cost: 1 }, ..],
        gas: gas,
    }
    where gas: Int;

    begin_return: {
        k: [Operation::Return, ..],
        word_stack: Stack::StackCons(start, Stack::StackCons(width, rest)),
        memory_used: used,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::Return, gas, cost: crate::MemoryExpansionCost { used, start, width } }, ..],
        word_stack: Stack::StackCons(start, Stack::StackCons(width, rest)),
        memory_used: used,
        gas: gas,
    }
    where start: Int, width: Int, rest: WordStack, used: Int, gas: Int;

    begin_revert: {
        k: [Operation::Revert, ..],
        word_stack: Stack::StackCons(start, Stack::StackCons(width, rest)),
        memory_used: used,
        gas: gas,
    } => {
        k: [crate::ChargeFixed { op: Operation::Revert, gas, cost: crate::MemoryExpansionCost { used, start, width } }, ..],
        word_stack: Stack::StackCons(start, Stack::StackCons(width, rest)),
        memory_used: used,
        gas: gas,
    }
    where start: Int, width: Int, rest: WordStack, used: Int, gas: Int;

    begin_static_call: {
        k: [Operation::StaticCall, ..],
        word_stack: stack,
        memory_used: used,
        accessed_accounts: accessed,
        gas: gas,
    } => {
        k: [crate::PrepareStaticCall { stack, accessed, used, gas }, ..],
        word_stack: stack,
        memory_used: used,
        accessed_accounts: accessed,
        gas: gas,
    }
    where stack: WordStack, used: Int, accessed: Set, gas: Int;

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

    exec_push_zero: {
        k: [GasResult::EnoughGas(Operation::PushZero, remaining), ..],
        word_stack: stack,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(0, stack),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, stack: WordStack, pc: Int, gas: Int;

    exec_pop: {
        k: [GasResult::EnoughGas(Operation::Pop, remaining), ..],
        word_stack: Stack::StackCons(head, tail),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: tail,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, head: Int, tail: WordStack, pc: Int, gas: Int;

    exec_duplicate: {
        k: [GasResult::EnoughGas(Operation::Duplicate { depth }, remaining), ..],
        word_stack: stack,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::StackAt { stack, index: int::sub(depth, 1) }, stack),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, depth: Int, stack: WordStack, pc: Int, gas: Int;

    exec_swap: {
        k: [GasResult::EnoughGas(Operation::Swap { depth }, remaining), ..],
        word_stack: Stack::StackCons(head, tail),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::StackAt { stack: tail, index: int::sub(depth, 1) }, crate::StackSet { stack: tail, index: int::sub(depth, 1), value: head },),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, depth: Int, head: Int, tail: WordStack, pc: Int, gas: Int;

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

    exec_exponent: {
        k: [GasResult::EnoughGas(Operation::Exponent, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(int::pow_mod(w0, w1, int::mul(int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616), int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616),),), rest,),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_sign_extend: {
        k: [GasResult::EnoughGas(Operation::SignExtend, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::WordSignExtend { index: w0, value: w1 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

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

    exec_bit_and: {
        k: [GasResult::EnoughGas(Operation::BitAnd, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(int::bit_and(w0, w1), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_bit_or: {
        k: [GasResult::EnoughGas(Operation::BitOr, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(int::bit_or(w0, w1), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_bit_xor: {
        k: [GasResult::EnoughGas(Operation::BitXor, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(int::bit_xor(w0, w1), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_bit_not: {
        k: [GasResult::EnoughGas(Operation::BitNot, remaining), ..],
        word_stack: Stack::StackCons(w0, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(int::bit_xor(w0, int::sub(int::mul(int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616,), int::mul(18_446_744_073_709_551_616, 18_446_744_073_709_551_616,),), 1,),), rest,),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, rest: WordStack, pc: Int, gas: Int;

    exec_byte: {
        k: [GasResult::EnoughGas(Operation::Byte, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::WordByte { index: w0, value: w1 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_shift_left: {
        k: [GasResult::EnoughGas(Operation::ShiftLeft, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::WordShiftLeft { value: w1, shift: w0 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_shift_right: {
        k: [GasResult::EnoughGas(Operation::ShiftRight, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::WordShiftRight { value: w1, shift: w0 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_signed_shift_right: {
        k: [GasResult::EnoughGas(Operation::SignedShiftRight, remaining), ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(crate::WordSignedShiftRight { value: w1, shift: w0 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, w0: Int, w1: Int, rest: WordStack, pc: Int, gas: Int;

    exec_address: {
        k: [GasResult::EnoughGas(Operation::Address, remaining), ..],
        word_stack: stack,
        address: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        address: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    #[k::requires(int::eq(account, present_account))]
    #[k::rule(label = "balance-true")]
    exec_balance_present: {
        k: [GasResult::EnoughGas(Operation::AccountBalance, remaining), ..],
        account_id: present_account,
        balance: balance,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(account, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        account_id: present_account,
        balance: balance,
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        word_stack: Stack::StackCons(balance, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, present_account: Int, balance: Int, accessed: Set, account: Int, rest: WordStack, pc: Int, gas: Int;

    #[k::rule(owise, label = "balance-false")]
    exec_balance_absent: {
        k: [GasResult::EnoughGas(Operation::AccountBalance, remaining), ..],
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(account, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, account: Int, accessed: Set, rest: WordStack, pc: Int, gas: Int;

    exec_origin: {
        k: [GasResult::EnoughGas(Operation::TxOrigin, remaining), ..],
        word_stack: stack,
        origin: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        origin: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_caller: {
        k: [GasResult::EnoughGas(Operation::MsgCaller, remaining), ..],
        word_stack: stack,
        caller: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        caller: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_call_value: {
        k: [GasResult::EnoughGas(Operation::MsgCallValue, remaining), ..],
        word_stack: stack,
        call_value: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        call_value: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_call_data_load: {
        k: [GasResult::EnoughGas(Operation::CallDataLoad, remaining), ..],
        call_data: call_data,
        word_stack: Stack::StackCons(index, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        call_data: call_data,
        word_stack: Stack::StackCons(crate::ReadMemoryWord { memory: call_data, index, remaining: 32, value: 0 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, call_data: Bytes, index: Int, rest: WordStack, pc: Int, gas: Int;

    exec_call_data_size: {
        k: [GasResult::EnoughGas(Operation::CallDataSize, remaining), ..],
        word_stack: stack,
        call_data: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(bytes::length(value), stack),
        call_data: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Bytes, stack: WordStack, pc: Int, gas: Int;

    exec_call_data_copy: {
        k: [GasResult::EnoughGas(Operation::CallDataCopy, remaining), ..],
        call_data: call_data,
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        call_data: call_data,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory, used, start: destination, width }, destination, source: call_data, source_index, remaining: width },
        memory_used: crate::MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, call_data: Bytes, memory: Bytes, used: Int, destination: Int, source_index: Int, width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_code_size: {
        k: [GasResult::EnoughGas(Operation::CodeSize, remaining), ..],
        program: value,
        word_stack: stack,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        program: value,
        word_stack: Stack::StackCons(bytes::length(value), stack),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Bytes, stack: WordStack, pc: Int, gas: Int;

    exec_code_copy: {
        k: [GasResult::EnoughGas(Operation::CodeCopy, remaining), ..],
        program: program,
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        program: program,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory, used, start: destination, width }, destination, source: program, source_index, remaining: width },
        memory_used: crate::MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, program: Bytes, memory: Bytes, used: Int, destination: Int, source_index: Int, width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_gas_price: {
        k: [GasResult::EnoughGas(Operation::TxGasPrice, remaining), ..],
        word_stack: stack,
        gas_price: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        gas_price: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    #[k::requires(int::eq(account, present_account))]
    #[k::rule(label = "extcodesize-true")]
    exec_external_code_size_present: {
        k: [GasResult::EnoughGas(Operation::ExternalCodeSize, remaining), ..],
        account_id: present_account,
        code: code,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(account, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        account_id: present_account,
        code: code,
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        word_stack: Stack::StackCons(bytes::length(code), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, present_account: Int, code: Bytes, accessed: Set, account: Int, rest: WordStack, pc: Int, gas: Int;

    #[k::rule(owise, label = "extcodesize-false")]
    exec_external_code_size_absent: {
        k: [GasResult::EnoughGas(Operation::ExternalCodeSize, remaining), ..],
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(account, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, account: Int, accessed: Set, rest: WordStack, pc: Int, gas: Int;

    #[k::requires(int::eq(account, present_account))]
    #[k::rule(label = "extcodecopy-true")]
    exec_external_code_copy_present: {
        k: [GasResult::EnoughGas(Operation::ExternalCodeCopy, remaining), ..],
        account_id: present_account,
        code: code,
        accessed_accounts: accessed,
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(account, Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest)))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        account_id: present_account,
        code: code,
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory, used, start: destination, width }, destination, source: code, source_index, remaining: width },
        memory_used: crate::MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, present_account: Int, code: Bytes, accessed: Set, account: Int, memory: Bytes, used: Int, destination: Int, source_index: Int, width: Int, rest: WordStack, pc: Int, gas: Int;

    #[k::rule(owise, label = "extcodecopy-false")]
    exec_external_code_copy_absent: {
        k: [GasResult::EnoughGas(Operation::ExternalCodeCopy, remaining), ..],
        accessed_accounts: accessed,
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(account, Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest)))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory, used, start: destination, width }, destination, source: bytes::empty(), source_index, remaining: width },
        memory_used: crate::MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, account: Int, accessed: Set, memory: Bytes, used: Int, destination: Int, source_index: Int, width: Int, rest: WordStack, pc: Int, gas: Int;

    #[k::requires(bool::and(
    int::eq(account, present_account),
    bool::not(crate::AccountEmpty { code, nonce, balance }),
    ))]
    #[k::rule(label = "extcodehash-true")]
    exec_external_code_hash_nonempty: {
        k: [GasResult::EnoughGas(Operation::ExternalCodeHash, remaining), ..],
        account_id: present_account,
        balance: balance,
        code: code,
        nonce: nonce,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(account, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        account_id: present_account,
        balance: balance,
        code: code,
        nonce: nonce,
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        word_stack: Stack::StackCons(crate::Keccak(code), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, present_account: Int, balance: Int, code: Bytes, nonce: Int, accessed: Set, account: Int, rest: WordStack, pc: Int, gas: Int;

    #[k::rule(owise, label = "extcodehash-false")]
    exec_external_code_hash_empty_or_absent: {
        k: [GasResult::EnoughGas(Operation::ExternalCodeHash, remaining), ..],
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(account, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, account: Int, accessed: Set, rest: WordStack, pc: Int, gas: Int;

    exec_return_data_size: {
        k: [GasResult::EnoughGas(Operation::ReturnDataSize, remaining), ..],
        word_stack: stack,
        output: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(bytes::length(value), stack),
        output: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Bytes, stack: WordStack, pc: Int, gas: Int;

    inspect_return_data_copy: {
        k: [GasResult::EnoughGas(Operation::ReturnDataCopy, remaining), ..],
        output: output,
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
    } => {
        k: [crate::ResolveReturnDataCopy { output, source_index, width, remaining }, ..],
        output: output,
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
    }
    where remaining: Int, output: Bytes, destination: Int, source_index: Int, width: Int, rest: WordStack;

    exec_return_data_copy_valid: {
        k: [CopyResult::ReturnDataCopyValid { remaining }, ..],
        output: output,
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        output: output,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory, used, start: destination, width }, destination, source: output, source_index, remaining: width },
        memory_used: crate::MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, output: Bytes, memory: Bytes, used: Int, destination: Int, source_index: Int, width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_return_data_copy_invalid: {
        k: [CopyResult::ReturnDataCopyInvalid { remaining }, ..],
        memory_used: used,
        word_stack: Stack::StackCons(destination, Stack::StackCons(source_index, Stack::StackCons(width, rest))),
        gas: gas,
        status_code: status,
    } => {
        k: [..],
        memory_used: crate::MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        gas: remaining,
        status_code: Status::InvalidMemoryAccess(),
    }
    where remaining: Int, used: Int, destination: Int, source_index: Int, width: Int, rest: WordStack, gas: Int, status: StatusCode;

    exec_block_hash: {
        k: [GasResult::EnoughGas(Operation::BlockHash, remaining), ..],
        block_hashes: hashes,
        number: number,
        word_stack: Stack::StackCons(requested, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        block_hashes: hashes,
        number: number,
        word_stack: Stack::StackCons(crate::BlockHashLookup { hashes, requested, highest: int::sub(number, 1), age: 0, }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, hashes: List, number: Int, requested: Int, rest: WordStack, pc: Int, gas: Int;

    exec_coinbase: {
        k: [GasResult::EnoughGas(Operation::BlockCoinbase, remaining), ..],
        word_stack: stack,
        coinbase: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        coinbase: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_timestamp: {
        k: [GasResult::EnoughGas(Operation::BlockTimestamp, remaining), ..],
        word_stack: stack,
        timestamp: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        timestamp: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_number: {
        k: [GasResult::EnoughGas(Operation::BlockNumber, remaining), ..],
        word_stack: stack,
        number: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        number: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_prev_randao: {
        k: [GasResult::EnoughGas(Operation::PrevRandao, remaining), ..],
        word_stack: stack,
        prev_randao: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        prev_randao: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_gas_limit: {
        k: [GasResult::EnoughGas(Operation::BlockGasLimit, remaining), ..],
        word_stack: stack,
        gas_limit: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        gas_limit: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_chain_id: {
        k: [GasResult::EnoughGas(Operation::NetworkChainId, remaining), ..],
        word_stack: stack,
        chain_id: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        chain_id: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    #[k::requires(int::eq(account, present_account))]
    exec_self_balance: {
        k: [GasResult::EnoughGas(Operation::SelfBalance, remaining), ..],
        address: account,
        account_id: present_account,
        balance: balance,
        word_stack: stack,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        address: account,
        account_id: present_account,
        balance: balance,
        word_stack: Stack::StackCons(balance, stack),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, account: Int, present_account: Int, balance: Int, stack: WordStack, pc: Int, gas: Int;

    exec_base_fee: {
        k: [GasResult::EnoughGas(Operation::BlockBaseFee, remaining), ..],
        word_stack: stack,
        base_fee: value,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(value, stack),
        base_fee: value,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, value: Int, stack: WordStack, pc: Int, gas: Int;

    exec_memory_load: {
        k: [GasResult::EnoughGas(Operation::MemoryLoad, remaining), ..],
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(index, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        local_mem: memory,
        memory_used: crate::MemoryUsageUpdate { used, start: index, width: 32 },
        word_stack: Stack::StackCons(crate::ReadMemoryWord { memory, index, remaining: 32, value: 0 }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, memory: Bytes, used: Int, index: Int, rest: WordStack, pc: Int, gas: Int;

    exec_memory_store: {
        k: [GasResult::EnoughGas(Operation::MemoryStore, remaining), ..],
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(index, Stack::StackCons(value, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        local_mem: crate::WriteMemoryWord { memory: bytes::pad_right(memory, int::mul(crate::MemoryUsageUpdate { used, start: index, width: 32 }, 32), 0), index, remaining: 32, value: crate::Chop(value) },
        memory_used: crate::MemoryUsageUpdate { used, start: index, width: 32 },
        word_stack: rest,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, memory: Bytes, used: Int, index: Int, value: Int, rest: WordStack, pc: Int, gas: Int;

    exec_memory_store8: {
        k: [GasResult::EnoughGas(Operation::MemoryStore8, remaining), ..],
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(index, Stack::StackCons(value, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        local_mem: bytes::update(bytes::pad_right(memory, int::mul(crate::MemoryUsageUpdate { used, start: index, width: 1 }, 32), 0), index, int::modulo(value, 256)),
        memory_used: crate::MemoryUsageUpdate { used, start: index, width: 1 },
        word_stack: rest,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, memory: Bytes, used: Int, index: Int, value: Int, rest: WordStack, pc: Int, gas: Int;

    exec_sha3: {
        k: [GasResult::EnoughGas(Operation::Sha3, remaining), ..],
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(start, Stack::StackCons(width, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        local_mem: memory,
        memory_used: crate::MemoryUsageUpdate { used, start, width },
        word_stack: Stack::StackCons(crate::Keccak(crate::ReturnBytes { memory, start, width }), rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, memory: Bytes, used: Int, start: Int, width: Int, rest: WordStack, pc: Int, gas: Int;

    #[k::requires(int::eq(current_account, account_id))]
    exec_storage_load: {
        k: [GasResult::EnoughGas(Operation::StorageLoad, remaining), ..],
        address: current_account,
        account_id: account_id,
        storage: storage,
        accessed_storage: accessed,
        word_stack: Stack::StackCons(index, rest),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        address: current_account,
        account_id: account_id,
        storage: storage,
        accessed_storage: crate::MarkStorageAccess { accessed, account: current_account, index },
        word_stack: Stack::StackCons(crate::StorageValue { storage, index }, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, current_account: Int, account_id: Int, storage: Map, accessed: Map, index: Int, rest: WordStack, pc: Int, gas: Int;

    #[k::requires(int::eq(current_account, account_id))]
    exec_storage_store: {
        k: [GasResult::EnoughGas(Operation::StorageStore, remaining), ..],
        address: current_account,
        account_id: account_id,
        storage: storage,
        original_storage: original_storage,
        accessed_storage: accessed,
        refund: refund,
        word_stack: Stack::StackCons(index, Stack::StackCons(new, rest)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        address: current_account,
        account_id: account_id,
        storage: map::update(storage, index, new),
        original_storage: original_storage,
        accessed_storage: crate::MarkStorageAccess { accessed, account: current_account, index },
        refund: int::add(refund, crate::StorageRefundDelta { original: crate::StorageValue { storage: original_storage, index }, current: crate::StorageValue { storage, index }, new }),
        word_stack: rest,
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, current_account: Int, account_id: Int, storage: Map, original_storage: Map, accessed: Map, refund: Int, index: Int, new: Int, rest: WordStack, pc: Int, gas: Int;

    exec_log: {
        k: [GasResult::EnoughGas(Operation::LogOpcode { topics }, remaining), ..],
        address: address,
        logs: logs,
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(start, Stack::StackCons(width, topic_stack)),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        address: address,
        logs: list::concat(logs, list::item(LogRecord::Entry { address, topics: crate::StackTakeList { stack: topic_stack, remaining: topics }, data: crate::ReturnBytes { memory, start, width }, }),),
        local_mem: memory,
        memory_used: crate::MemoryUsageUpdate { used, start, width },
        word_stack: crate::StackDrop { stack: topic_stack, remaining: topics },
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, topics: Int, address: Int, logs: List, memory: Bytes, used: Int, start: Int, width: Int, topic_stack: WordStack, pc: Int, gas: Int;

    exec_memory_size: {
        k: [GasResult::EnoughGas(Operation::MemorySize, remaining), ..],
        memory_used: used,
        word_stack: stack,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        memory_used: used,
        word_stack: Stack::StackCons(crate::Chop(int::mul(32, used)), stack),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, used: Int, stack: WordStack, pc: Int, gas: Int;

    exec_gas_remaining: {
        k: [GasResult::EnoughGas(Operation::GasRemaining, remaining), ..],
        word_stack: stack,
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        word_stack: Stack::StackCons(remaining, stack),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, stack: WordStack, pc: Int, gas: Int;

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

    inspect_jump_destination: {
        k: [GasResult::EnoughGas(Operation::Jump, remaining), ..],
        program: program,
        word_stack: Stack::StackCons(destination, rest),
        gas: gas,
    } => {
        k: [crate::ResolveJump { program, destination }, ..],
        program: program,
        word_stack: rest,
        gas: remaining,
    }
    where remaining: Int, program: Bytes, destination: Int, rest: WordStack, gas: Int;

    inspect_jump_if_destination: {
        k: [GasResult::EnoughGas(Operation::JumpIf, remaining), ..],
        program: program,
        word_stack: Stack::StackCons(destination, Stack::StackCons(condition, rest)),
        gas: gas,
    } => {
        k: [crate::ResolveJumpIf { program, destination, condition }, ..],
        program: program,
        word_stack: rest,
        gas: remaining,
    }
    where remaining: Int, program: Bytes, destination: Int, condition: Int, rest: WordStack, gas: Int;

    exec_valid_jump: {
        k: [JumpResult::JumpValid { destination }, ..],
        pc: pc,
    } => {
        k: [ExecutionCommand::Run(), ..],
        pc: destination,
    }
    where destination: Int, pc: Int;

    exec_false_jump_if: {
        k: [JumpResult::JumpFallthrough(), ..],
        pc: pc,
    } => {
        k: [ExecutionCommand::Run(), ..],
        pc: int::add(pc, 1),
    }
    where pc: Int;

    exec_invalid_jump: {
        k: [JumpResult::JumpInvalid(), ..],
        status_code: status,
    } => {
        k: [..],
        status_code: Status::BadJumpDestination(),
    }
    where status: StatusCode;

    exec_jump_dest: {
        k: [GasResult::EnoughGas(Operation::JumpDest, remaining), ..],
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, pc: Int, gas: Int;

    exec_return: {
        k: [GasResult::EnoughGas(Operation::Return, remaining), ..],
        output: output,
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(start, Stack::StackCons(width, rest)),
        gas: gas,
        status_code: status,
    } => {
        k: [..],
        output: crate::ReturnBytes { memory, start, width },
        local_mem: memory,
        memory_used: crate::MemoryUsageUpdate { used, start, width },
        word_stack: rest,
        gas: remaining,
        status_code: Status::Success(),
    }
    where remaining: Int, output: Bytes, memory: Bytes, used: Int, start: Int, width: Int, rest: WordStack, gas: Int, status: StatusCode;

    exec_revert: {
        k: [GasResult::EnoughGas(Operation::Revert, remaining), ..],
        output: output,
        local_mem: memory,
        memory_used: used,
        word_stack: Stack::StackCons(start, Stack::StackCons(width, rest)),
        gas: gas,
        status_code: status,
    } => {
        k: [..],
        output: crate::ReturnBytes { memory, start, width },
        local_mem: memory,
        memory_used: crate::MemoryUsageUpdate { used, start, width },
        word_stack: rest,
        gas: remaining,
        status_code: Status::Reverted(),
    }
    where remaining: Int, output: Bytes, memory: Bytes, used: Int, start: Int, width: Int, rest: WordStack, gas: Int, status: StatusCode;

    begin_static_call_ecrec: {
        k: [GasResult::EnoughEcrecPrecompileGas { remaining }, ..],
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(1, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    } => {
        k: [crate::ResolveEcrecPrecompile { requested: gas_cap, available: remaining, }, ..],
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(1, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    }
    where remaining: Int, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack;

    exec_static_call_ecrec_success: {
        k: [PrecompileResult::EcrecPrecompileSuccess { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(1, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(1)),
        output: crate::EcrecPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } },
        address: address,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, }, destination: return_start, source: crate::EcrecPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }, source_index: 0, remaining: crate::Minimum { left: return_width, right: bytes::length(crate::EcrecPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }) }, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 1 },
        word_stack: Stack::StackCons(1, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_static_call_ecrec_exception: {
        k: [PrecompileResult::EcrecPrecompileFailure { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(1, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(1)),
        output: bytes::empty(),
        address: address,
        local_mem: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 1 },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    begin_static_call_sha256: {
        k: [GasResult::EnoughSha256PrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(2, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    } => {
        k: [crate::ResolveSha256Precompile { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width }, requested: gas_cap, available: remaining, }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(2, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    }
    where remaining: Int, memory: Bytes, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack;

    exec_static_call_sha256_success: {
        k: [PrecompileResult::Sha256PrecompileSuccess { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(2, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(2)),
        output: crate::Sha256Digest { value: crate::ReturnBytes { memory, start: argument_start, width: argument_width } },
        address: address,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, }, destination: return_start, source: crate::Sha256Digest { value: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }, source_index: 0, remaining: crate::Minimum { left: return_width, right: 32 }, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 2 },
        word_stack: Stack::StackCons(1, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_static_call_sha256_exception: {
        k: [PrecompileResult::Sha256PrecompileFailure { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(2, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(2)),
        output: bytes::empty(),
        address: address,
        local_mem: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 2 },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    begin_static_call_ripemd160: {
        k: [GasResult::EnoughRipemd160PrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(3, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    } => {
        k: [crate::ResolveRipemd160Precompile { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width }, requested: gas_cap, available: remaining, }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(3, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    }
    where remaining: Int, memory: Bytes, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack;

    exec_static_call_ripemd160_success: {
        k: [PrecompileResult::Ripemd160PrecompileSuccess { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(3, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(3)),
        output: crate::CopyBytes { memory: bytes::pad_right(bytes::empty(), 32, 0), destination: 12, source: crate::Ripemd160Digest { value: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }, source_index: 0, remaining: 20 },
        address: address,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, }, destination: return_start, source: crate::CopyBytes { memory: bytes::pad_right(bytes::empty(), 32, 0), destination: 12, source: crate::Ripemd160Digest { value: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }, source_index: 0, remaining: 20 }, source_index: 0, remaining: crate::Minimum { left: return_width, right: 32 }, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 3 },
        word_stack: Stack::StackCons(1, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_static_call_ripemd160_exception: {
        k: [PrecompileResult::Ripemd160PrecompileFailure { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(3, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(3)),
        output: bytes::empty(),
        address: address,
        local_mem: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 3 },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    begin_static_call_identity: {
        k: [GasResult::EnoughIdentityPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(4, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    } => {
        k: [crate::ResolveIdentityPrecompile { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width }, requested: gas_cap, available: remaining, }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(4, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    }
    where remaining: Int, memory: Bytes, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack;

    exec_static_call_identity_success: {
        k: [PrecompileResult::IdentityPrecompileSuccess { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(4, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(4)),
        output: crate::ReturnBytes { memory, start: argument_start, width: argument_width },
        address: address,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, }, destination: return_start, source: crate::ReturnBytes { memory, start: argument_start, width: argument_width }, source_index: 0, remaining: crate::Minimum { left: return_width, right: argument_width }, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 4 },
        word_stack: Stack::StackCons(1, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_static_call_identity_exception: {
        k: [PrecompileResult::IdentityPrecompileFailure { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(4, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(4)),
        output: bytes::empty(),
        address: address,
        local_mem: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 4 },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    begin_static_call_modexp: {
        k: [GasResult::EnoughModExpPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(5, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    } => {
        k: [crate::ResolveModExpPrecompile { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width }, requested: gas_cap, available: remaining, }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(5, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    }
    where remaining: Int, memory: Bytes, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack;

    exec_static_call_modexp_success: {
        k: [PrecompileResult::ModExpPrecompileSuccess { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(5, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(5)),
        output: crate::ModExpPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } },
        address: address,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, }, destination: return_start, source: crate::ModExpPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }, source_index: 0, remaining: crate::Minimum { left: return_width, right: bytes::length(crate::ModExpPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }) }, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 5 },
        word_stack: Stack::StackCons(1, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_static_call_modexp_exception: {
        k: [PrecompileResult::ModExpPrecompileFailure { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(5, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(5)),
        output: bytes::empty(),
        address: address,
        local_mem: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 5 },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    begin_static_call_ecadd: {
        k: [GasResult::EnoughEcAddPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(6, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    } => {
        k: [crate::ResolveEcAddPrecompile { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width }, requested: gas_cap, available: remaining, }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(6, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    }
    where remaining: Int, memory: Bytes, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack;

    exec_static_call_ecadd_success: {
        k: [PrecompileResult::EcAddPrecompileSuccess { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(6, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(6)),
        output: crate::EcAddPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } },
        address: address,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, }, destination: return_start, source: crate::EcAddPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }, source_index: 0, remaining: crate::Minimum { left: return_width, right: 64 }, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 6 },
        word_stack: Stack::StackCons(1, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_static_call_ecadd_exception: {
        k: [PrecompileResult::EcAddPrecompileFailure { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(6, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(6)),
        output: bytes::empty(),
        address: address,
        local_mem: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 6 },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    begin_static_call_ecmul: {
        k: [GasResult::EnoughEcMulPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(7, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    } => {
        k: [crate::ResolveEcMulPrecompile { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width }, requested: gas_cap, available: remaining, }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(7, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    }
    where remaining: Int, memory: Bytes, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack;

    exec_static_call_ecmul_success: {
        k: [PrecompileResult::EcMulPrecompileSuccess { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(7, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(7)),
        output: crate::EcMulPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } },
        address: address,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, }, destination: return_start, source: crate::EcMulPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }, source_index: 0, remaining: crate::Minimum { left: return_width, right: 64 }, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 7 },
        word_stack: Stack::StackCons(1, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_static_call_ecmul_exception: {
        k: [PrecompileResult::EcMulPrecompileFailure { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(7, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(7)),
        output: bytes::empty(),
        address: address,
        local_mem: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 7 },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    begin_static_call_ecpairing: {
        k: [GasResult::EnoughEcPairingPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(8, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    } => {
        k: [crate::ResolveEcPairingPrecompile { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width }, requested: gas_cap, available: remaining, }, ..],
        local_mem: memory,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(8, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
    }
    where remaining: Int, memory: Bytes, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack;

    exec_static_call_ecpairing_success: {
        k: [PrecompileResult::EcPairingPrecompileSuccess { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(8, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(8)),
        output: crate::EcPairingPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } },
        address: address,
        local_mem: crate::CopyBytes { memory: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, }, destination: return_start, source: crate::EcPairingPrecompileOutput { data: crate::ReturnBytes { memory, start: argument_start, width: argument_width } }, source_index: 0, remaining: crate::Minimum { left: return_width, right: 32 }, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 8 },
        word_stack: Stack::StackCons(1, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_static_call_ecpairing_exception: {
        k: [PrecompileResult::EcPairingPrecompileFailure { remaining }, ..],
        touched_accounts: touched_accounts,
        output: output,
        address: address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(8, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(8)),
        output: bytes::empty(),
        address: address,
        local_mem: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, },
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account: 8 },
        word_stack: Stack::StackCons(0, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, touched_accounts: Set, output: Bytes, address: Int, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    #[k::requires(bool::and(
    int::gt(account, 9),
    bool::and(
    int::eq(account, present_account),
    bool::not(crate::AccountEmpty { code, nonce, balance }),
    ),
    ))]
    exec_static_call_nonempty: {
        k: [GasResult::EnoughGas(Operation::StaticCall, remaining), ..],
        call_stack: call_stack,
        interim_states: interim_states,
        touched_accounts: touched_accounts,
        account_id: present_account,
        balance: balance,
        code: code,
        nonce: nonce,
        storage: storage,
        original_storage: original_storage,
        output: output,
        status_code: status,
        program: program,
        jump_dests: jump_dests,
        address: address,
        caller: caller,
        call_data: call_data,
        call_value: call_value,
        local_mem: memory,
        memory_used: used,
        self_destruct: self_destruct,
        logs: logs,
        refund: refund,
        accessed_accounts: accessed,
        accessed_storage: accessed_storage,
        created_accounts: created_accounts,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(account, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
        call_gas: old_call_gas,
        static_mode: static_mode,
        call_depth: call_depth,
        code_address: code_address,
    } => {
        k: [ExecutionCommand::Run(), ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        call_stack: list::concat(list::item(k::fragment![CallState { program: program, jump_dests: jump_dests, address: address, caller: caller, call_data: call_data, call_value: call_value, word_stack: rest, local_mem: crate::PrepareCopyMemory { memory: crate::PrepareCopyMemory { memory, used, start: argument_start, width: argument_width }, used: crate::MemoryUsageUpdate { used, start: argument_start, width: argument_width }, start: return_start, width: return_width, }, pc: int::add(pc, 1), gas: int::sub(remaining, crate::StaticCallGas { requested: gas_cap, available: remaining }), memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width }, call_gas: crate::StaticCallGas { requested: gas_cap, available: remaining }, static_mode: static_mode, call_depth: call_depth, code_address: code_address, }]), call_stack,),
        interim_states: list::concat(list::item(SavedWorldState::Snapshot { account_id: present_account, balance: balance, code: code, nonce: nonce, storage: storage, original_storage: original_storage, self_destruct: self_destruct, logs: logs, refund: refund, accessed_accounts: crate::MarkAccountAccess { accessed, account }, accessed_storage: accessed_storage, created_accounts: created_accounts, }), interim_states,),
        touched_accounts: set::concat(set::concat(touched_accounts, set::item(address)), set::item(account)),
        account_id: present_account,
        balance: balance,
        code: code,
        nonce: nonce,
        storage: storage,
        original_storage: original_storage,
        output: bytes::empty(),
        status_code: Status::Running(),
        program: code,
        jump_dests: bytes::empty(),
        address: account,
        caller: address,
        call_data: crate::ReturnBytes { memory, start: argument_start, width: argument_width },
        call_value: 0,
        local_mem: bytes::empty(),
        memory_used: 0,
        self_destruct: self_destruct,
        logs: logs,
        refund: refund,
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        accessed_storage: accessed_storage,
        created_accounts: created_accounts,
        word_stack: Stack::StackEmpty(),
        pc: 0,
        gas: crate::StaticCallGas { requested: gas_cap, available: remaining },
        call_gas: 0,
        static_mode: true,
        call_depth: int::add(call_depth, 1),
        code_address: account,
    }
    where remaining: Int, call_stack: List, interim_states: List, touched_accounts: Set, present_account: Int, balance: Int, code: Bytes, nonce: Int, storage: Map, original_storage: Map, output: Bytes, status: StatusCode, program: Bytes, jump_dests: Bytes, address: Int, caller: Int, call_data: Bytes, call_value: Int, memory: Bytes, used: Int, self_destruct: Set, logs: List, refund: Int, accessed: Set, accessed_storage: Map, created_accounts: Set, gas_cap: Int, account: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int, old_call_gas: Int, static_mode: Bool, call_depth: Int, code_address: Int;

    finish_static_call_success: {
        k: [ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        call_stack: k::term![list::concat(list::item(k::fragment![CallState { program: caller_program, jump_dests: caller_jump_dests, address: caller_address, caller: caller_caller, call_data: caller_call_data, call_value: caller_call_value, word_stack: caller_stack, local_mem: caller_memory, pc: caller_pc, gas: caller_gas, memory_used: caller_memory_used, call_gas: caller_call_gas, static_mode: caller_static_mode, call_depth: caller_call_depth, code_address: caller_code_address, }]), remaining_call_stack,)],
        interim_states: k::term![list::concat(list::item(saved_world_state), remaining_interim_states)],
        output: child_output,
        status_code: Status::Success(),
        program: child_program,
        jump_dests: child_jump_dests,
        address: child_address,
        caller: child_caller,
        call_data: child_call_data,
        call_value: child_call_value,
        word_stack: child_stack,
        local_mem: child_memory,
        pc: child_pc,
        gas: child_gas,
        memory_used: child_memory_used,
        call_gas: child_call_gas,
        static_mode: child_static_mode,
        call_depth: child_call_depth,
        code_address: child_code_address,
    } => {
        k: [ExecutionCommand::Run(), ..],
        call_stack: remaining_call_stack,
        interim_states: remaining_interim_states,
        output: child_output,
        status_code: Status::Running(),
        program: caller_program,
        jump_dests: caller_jump_dests,
        address: caller_address,
        caller: caller_caller,
        call_data: caller_call_data,
        call_value: caller_call_value,
        word_stack: Stack::StackCons(1, caller_stack),
        local_mem: crate::CopyBytes { memory: caller_memory, destination: return_start, source: child_output, source_index: 0, remaining: crate::Minimum { left: return_width, right: bytes::length(child_output) }, },
        pc: caller_pc,
        gas: int::add(caller_gas, child_gas),
        memory_used: caller_memory_used,
        call_gas: caller_call_gas,
        static_mode: caller_static_mode,
        call_depth: caller_call_depth,
        code_address: caller_code_address,
    }
    where return_start: Int, return_width: Int, remaining_call_stack: List, saved_world_state: WorldState, remaining_interim_states: List, child_output: Bytes, child_program: Bytes, child_jump_dests: Bytes, child_address: Int, child_caller: Int, child_call_data: Bytes, child_call_value: Int, child_stack: WordStack, child_memory: Bytes, child_pc: Int, child_gas: Int, child_memory_used: Int, child_call_gas: Int, child_static_mode: Bool, child_call_depth: Int, child_code_address: Int, caller_program: Bytes, caller_jump_dests: Bytes, caller_address: Int, caller_caller: Int, caller_call_data: Bytes, caller_call_value: Int, caller_stack: WordStack, caller_memory: Bytes, caller_pc: Int, caller_gas: Int, caller_memory_used: Int, caller_call_gas: Int, caller_static_mode: Bool, caller_call_depth: Int, caller_code_address: Int;

    finish_static_call_revert: {
        k: [ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        call_stack: k::term![list::concat(list::item(k::fragment![CallState { program: caller_program, jump_dests: caller_jump_dests, address: caller_address, caller: caller_caller, call_data: caller_call_data, call_value: caller_call_value, word_stack: caller_stack, local_mem: caller_memory, pc: caller_pc, gas: caller_gas, memory_used: caller_memory_used, call_gas: caller_call_gas, static_mode: caller_static_mode, call_depth: caller_call_depth, code_address: caller_code_address, }]), remaining_call_stack,)],
        interim_states: k::term![list::concat(list::item(SavedWorldState::Snapshot { account_id: saved_account_id, balance: saved_balance, code: saved_code, nonce: saved_nonce, storage: saved_storage, original_storage: saved_original_storage, self_destruct: saved_self_destruct, logs: saved_logs, refund: saved_refund, accessed_accounts: saved_accessed_accounts, accessed_storage: saved_accessed_storage, created_accounts: saved_created_accounts, }), remaining_interim_states,)],
        account_id: child_account_id,
        balance: child_balance,
        code: child_code,
        nonce: child_nonce,
        storage: child_storage,
        original_storage: child_original_storage,
        self_destruct: child_self_destruct,
        logs: child_logs,
        refund: child_refund,
        accessed_accounts: child_accessed_accounts,
        accessed_storage: child_accessed_storage,
        created_accounts: child_created_accounts,
        output: child_output,
        status_code: Status::Reverted(),
        program: child_program,
        jump_dests: child_jump_dests,
        address: child_address,
        caller: child_caller,
        call_data: child_call_data,
        call_value: child_call_value,
        word_stack: child_stack,
        local_mem: child_memory,
        pc: child_pc,
        gas: child_gas,
        memory_used: child_memory_used,
        call_gas: child_call_gas,
        static_mode: child_static_mode,
        call_depth: child_call_depth,
        code_address: child_code_address,
    } => {
        k: [ExecutionCommand::Run(), ..],
        call_stack: remaining_call_stack,
        interim_states: remaining_interim_states,
        account_id: saved_account_id,
        balance: saved_balance,
        code: saved_code,
        nonce: saved_nonce,
        storage: saved_storage,
        original_storage: saved_original_storage,
        self_destruct: saved_self_destruct,
        logs: saved_logs,
        refund: saved_refund,
        accessed_accounts: saved_accessed_accounts,
        accessed_storage: saved_accessed_storage,
        created_accounts: saved_created_accounts,
        output: child_output,
        status_code: Status::Running(),
        program: caller_program,
        jump_dests: caller_jump_dests,
        address: caller_address,
        caller: caller_caller,
        call_data: caller_call_data,
        call_value: caller_call_value,
        word_stack: Stack::StackCons(0, caller_stack),
        local_mem: crate::CopyBytes { memory: caller_memory, destination: return_start, source: child_output, source_index: 0, remaining: crate::Minimum { left: return_width, right: bytes::length(child_output) }, },
        pc: caller_pc,
        gas: int::add(caller_gas, child_gas),
        memory_used: caller_memory_used,
        call_gas: caller_call_gas,
        static_mode: caller_static_mode,
        call_depth: caller_call_depth,
        code_address: caller_code_address,
    }
    where return_start: Int, return_width: Int, remaining_call_stack: List, remaining_interim_states: List, saved_account_id: Int, saved_balance: Int, saved_code: Bytes, saved_nonce: Int, saved_storage: Map, saved_original_storage: Map, saved_self_destruct: Set, saved_logs: List, saved_refund: Int, saved_accessed_accounts: Set, saved_accessed_storage: Map, saved_created_accounts: Set, child_account_id: Int, child_balance: Int, child_code: Bytes, child_nonce: Int, child_storage: Map, child_original_storage: Map, child_self_destruct: Set, child_logs: List, child_refund: Int, child_accessed_accounts: Set, child_accessed_storage: Map, child_created_accounts: Set, child_output: Bytes, child_program: Bytes, child_jump_dests: Bytes, child_address: Int, child_caller: Int, child_call_data: Bytes, child_call_value: Int, child_stack: WordStack, child_memory: Bytes, child_pc: Int, child_gas: Int, child_memory_used: Int, child_call_gas: Int, child_static_mode: Bool, child_call_depth: Int, child_code_address: Int, caller_program: Bytes, caller_jump_dests: Bytes, caller_address: Int, caller_caller: Int, caller_call_data: Bytes, caller_call_value: Int, caller_stack: WordStack, caller_memory: Bytes, caller_pc: Int, caller_gas: Int, caller_memory_used: Int, caller_call_gas: Int, caller_static_mode: Bool, caller_call_depth: Int, caller_code_address: Int;

    finish_static_call_stack_underflow: {
        k: [ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        status_code: Status::StackUnderflow(),
    } => {
        k: [ExecutionCommand::FinishStaticCallExceptional { return_start, return_width }, ..],
        status_code: Status::StackUnderflow(),
    }
    where return_start: Int, return_width: Int;

    finish_static_call_stack_overflow: {
        k: [ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        status_code: Status::StackOverflow(),
    } => {
        k: [ExecutionCommand::FinishStaticCallExceptional { return_start, return_width }, ..],
        status_code: Status::StackOverflow(),
    }
    where return_start: Int, return_width: Int;

    finish_static_call_out_of_gas: {
        k: [ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        status_code: Status::OutOfGas(),
    } => {
        k: [ExecutionCommand::FinishStaticCallExceptional { return_start, return_width }, ..],
        status_code: Status::OutOfGas(),
    }
    where return_start: Int, return_width: Int;

    finish_static_call_bad_jump_destination: {
        k: [ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        status_code: Status::BadJumpDestination(),
    } => {
        k: [ExecutionCommand::FinishStaticCallExceptional { return_start, return_width }, ..],
        status_code: Status::BadJumpDestination(),
    }
    where return_start: Int, return_width: Int;

    finish_static_call_invalid_memory_access: {
        k: [ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        status_code: Status::InvalidMemoryAccess(),
    } => {
        k: [ExecutionCommand::FinishStaticCallExceptional { return_start, return_width }, ..],
        status_code: Status::InvalidMemoryAccess(),
    }
    where return_start: Int, return_width: Int;

    finish_static_call_invalid_instruction: {
        k: [ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        status_code: Status::InvalidInstruction(),
    } => {
        k: [ExecutionCommand::FinishStaticCallExceptional { return_start, return_width }, ..],
        status_code: Status::InvalidInstruction(),
    }
    where return_start: Int, return_width: Int;

    finish_static_call_static_violation: {
        k: [ExecutionCommand::FinishStaticCall { return_start, return_width }, ..],
        status_code: Status::StaticModeViolation(),
    } => {
        k: [ExecutionCommand::FinishStaticCallExceptional { return_start, return_width }, ..],
        status_code: Status::StaticModeViolation(),
    }
    where return_start: Int, return_width: Int;

    finish_static_call_exception: {
        k: [ExecutionCommand::FinishStaticCallExceptional { return_start, return_width }, ..],
        call_stack: k::term![list::concat(list::item(k::fragment![CallState { program: caller_program, jump_dests: caller_jump_dests, address: caller_address, caller: caller_caller, call_data: caller_call_data, call_value: caller_call_value, word_stack: caller_stack, local_mem: caller_memory, pc: caller_pc, gas: caller_gas, memory_used: caller_memory_used, call_gas: caller_call_gas, static_mode: caller_static_mode, call_depth: caller_call_depth, code_address: caller_code_address, }]), remaining_call_stack,)],
        interim_states: k::term![list::concat(list::item(SavedWorldState::Snapshot { account_id: saved_account_id, balance: saved_balance, code: saved_code, nonce: saved_nonce, storage: saved_storage, original_storage: saved_original_storage, self_destruct: saved_self_destruct, logs: saved_logs, refund: saved_refund, accessed_accounts: saved_accessed_accounts, accessed_storage: saved_accessed_storage, created_accounts: saved_created_accounts, }), remaining_interim_states,)],
        account_id: child_account_id,
        balance: child_balance,
        code: child_code,
        nonce: child_nonce,
        storage: child_storage,
        original_storage: child_original_storage,
        self_destruct: child_self_destruct,
        logs: child_logs,
        refund: child_refund,
        accessed_accounts: child_accessed_accounts,
        accessed_storage: child_accessed_storage,
        created_accounts: child_created_accounts,
        output: child_output,
        status_code: child_status,
        program: child_program,
        jump_dests: child_jump_dests,
        address: child_address,
        caller: child_caller,
        call_data: child_call_data,
        call_value: child_call_value,
        word_stack: child_stack,
        local_mem: child_memory,
        pc: child_pc,
        gas: child_gas,
        memory_used: child_memory_used,
        call_gas: child_call_gas,
        static_mode: child_static_mode,
        call_depth: child_call_depth,
        code_address: child_code_address,
    } => {
        k: [ExecutionCommand::Run(), ..],
        call_stack: remaining_call_stack,
        interim_states: remaining_interim_states,
        account_id: saved_account_id,
        balance: saved_balance,
        code: saved_code,
        nonce: saved_nonce,
        storage: saved_storage,
        original_storage: saved_original_storage,
        self_destruct: saved_self_destruct,
        logs: saved_logs,
        refund: saved_refund,
        accessed_accounts: saved_accessed_accounts,
        accessed_storage: saved_accessed_storage,
        created_accounts: saved_created_accounts,
        output: bytes::empty(),
        status_code: Status::Running(),
        program: caller_program,
        jump_dests: caller_jump_dests,
        address: caller_address,
        caller: caller_caller,
        call_data: caller_call_data,
        call_value: caller_call_value,
        word_stack: Stack::StackCons(0, caller_stack),
        local_mem: caller_memory,
        pc: caller_pc,
        gas: caller_gas,
        memory_used: caller_memory_used,
        call_gas: caller_call_gas,
        static_mode: caller_static_mode,
        call_depth: caller_call_depth,
        code_address: caller_code_address,
    }
    where return_start: Int, return_width: Int, remaining_call_stack: List, remaining_interim_states: List, saved_account_id: Int, saved_balance: Int, saved_code: Bytes, saved_nonce: Int, saved_storage: Map, saved_original_storage: Map, saved_self_destruct: Set, saved_logs: List, saved_refund: Int, saved_accessed_accounts: Set, saved_accessed_storage: Map, saved_created_accounts: Set, child_account_id: Int, child_balance: Int, child_code: Bytes, child_nonce: Int, child_storage: Map, child_original_storage: Map, child_self_destruct: Set, child_logs: List, child_refund: Int, child_accessed_accounts: Set, child_accessed_storage: Map, child_created_accounts: Set, child_output: Bytes, child_status: StatusCode, child_program: Bytes, child_jump_dests: Bytes, child_address: Int, child_caller: Int, child_call_data: Bytes, child_call_value: Int, child_stack: WordStack, child_memory: Bytes, child_pc: Int, child_gas: Int, child_memory_used: Int, child_call_gas: Int, child_static_mode: Bool, child_call_depth: Int, child_code_address: Int, caller_program: Bytes, caller_jump_dests: Bytes, caller_address: Int, caller_caller: Int, caller_call_data: Bytes, caller_call_value: Int, caller_stack: WordStack, caller_memory: Bytes, caller_pc: Int, caller_gas: Int, caller_memory_used: Int, caller_call_gas: Int, caller_static_mode: Bool, caller_call_depth: Int, caller_code_address: Int;

    #[k::requires(bool::and(
    int::gt(account, 9),
    bool::or(
    int::ne(account, present_account),
    bool::and(
    int::eq(account, present_account),
    crate::AccountEmpty { code, nonce, balance },
    ),
    ),
    ))]
    #[k::rule(owise)]
    exec_static_call_empty_or_absent: {
        k: [GasResult::EnoughGas(Operation::StaticCall, remaining), ..],
        account_id: present_account,
        balance: balance,
        code: code,
        nonce: nonce,
        output: output,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: Stack::StackCons(gas_cap, Stack::StackCons(account, Stack::StackCons(argument_start, Stack::StackCons(argument_width, Stack::StackCons(return_start, Stack::StackCons(return_width, rest)))))),
        pc: pc,
        gas: gas,
    } => {
        k: [ExecutionCommand::Run(), ..],
        account_id: present_account,
        balance: balance,
        code: code,
        nonce: nonce,
        output: bytes::empty(),
        local_mem: memory,
        memory_used: crate::CallMemoryUsage { used, argument_start, argument_width, return_start, return_width },
        accessed_accounts: crate::MarkAccountAccess { accessed, account },
        word_stack: Stack::StackCons(1, rest),
        pc: int::add(pc, 1),
        gas: remaining,
    }
    where remaining: Int, present_account: Int, balance: Int, code: Bytes, nonce: Int, output: Bytes, memory: Bytes, used: Int, accessed: Set, gas_cap: Int, account: Int, argument_start: Int, argument_width: Int, return_start: Int, return_width: Int, rest: WordStack, pc: Int, gas: Int;

    exec_stop: {
        k: [GasResult::EnoughGas(Operation::Stop, remaining), ..],
        gas: gas,
        output: output,
        status_code: status,
    } => {
        k: [..],
        gas: remaining,
        output: bytes::empty(),
        status_code: Status::Success(),
    }
    where remaining: Int, gas: Int, output: Bytes, status: StatusCode;
}

k::rules! {
    for Machine;
    balance_underflow: {
        k: [Operation::AccountBalance, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    external_code_size_underflow: {
        k: [Operation::ExternalCodeSize, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    external_code_hash_underflow: {
        k: [Operation::ExternalCodeHash, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    external_code_copy_underflow_empty: {
        k: [Operation::ExternalCodeCopy, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    external_code_copy_underflow_one: {
        k: [Operation::ExternalCodeCopy, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    external_code_copy_underflow_two: {
        k: [Operation::ExternalCodeCopy, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, w1: Int, status: StatusCode;

    external_code_copy_underflow_three: {
        k: [Operation::ExternalCodeCopy, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackCons(w2, Stack::StackEmpty()))),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackCons(w2, Stack::StackEmpty()))),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, w1: Int, w2: Int, status: StatusCode;

    call_data_load_underflow: {
        k: [Operation::CallDataLoad, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    call_data_copy_underflow_empty: {
        k: [Operation::CallDataCopy, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    call_data_copy_underflow_one: {
        k: [Operation::CallDataCopy, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    call_data_copy_underflow_two: {
        k: [Operation::CallDataCopy, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, w1: Int, status: StatusCode;

    code_copy_underflow_empty: {
        k: [Operation::CodeCopy, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    code_copy_underflow_one: {
        k: [Operation::CodeCopy, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    code_copy_underflow_two: {
        k: [Operation::CodeCopy, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, w1: Int, status: StatusCode;

    return_data_copy_underflow_empty: {
        k: [Operation::ReturnDataCopy, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    return_data_copy_underflow_one: {
        k: [Operation::ReturnDataCopy, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    return_data_copy_underflow_two: {
        k: [Operation::ReturnDataCopy, ..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackCons(w1, Stack::StackEmpty())),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, w1: Int, status: StatusCode;

    return_underflow_empty: {
        k: [Operation::Return, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    return_underflow_one: {
        k: [Operation::Return, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    revert_underflow_empty: {
        k: [Operation::Revert, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    revert_underflow_one: {
        k: [Operation::Revert, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    memory_load_underflow: {
        k: [Operation::MemoryLoad, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    memory_store_underflow_empty: {
        k: [Operation::MemoryStore, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    memory_store_underflow_one: {
        k: [Operation::MemoryStore, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    memory_store8_underflow_empty: {
        k: [Operation::MemoryStore8, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    memory_store8_underflow_one: {
        k: [Operation::MemoryStore8, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    sha3_underflow_empty: {
        k: [Operation::Sha3, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    sha3_underflow_one: {
        k: [Operation::Sha3, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    storage_load_underflow: {
        k: [Operation::StorageLoad, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    storage_store_underflow_empty: {
        k: [Operation::StorageStore, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    storage_store_underflow_one: {
        k: [Operation::StorageStore, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    block_hash_underflow: {
        k: [Operation::BlockHash, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    jump_underflow: {
        k: [Operation::Jump, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    jump_if_underflow_empty: {
        k: [Operation::JumpIf, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    jump_if_underflow_one: {
        k: [Operation::JumpIf, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

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

    exponent_underflow_empty: {
        k: [Operation::Exponent, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    exponent_underflow_one: {
        k: [Operation::Exponent, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    sign_extend_underflow_empty: {
        k: [Operation::SignExtend, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    sign_extend_underflow_one: {
        k: [Operation::SignExtend, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    bit_and_underflow_empty: {
        k: [Operation::BitAnd, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    bit_and_underflow_one: {
        k: [Operation::BitAnd, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    bit_or_underflow_empty: {
        k: [Operation::BitOr, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    bit_or_underflow_one: {
        k: [Operation::BitOr, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    bit_xor_underflow_empty: {
        k: [Operation::BitXor, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    bit_xor_underflow_one: {
        k: [Operation::BitXor, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    bit_not_underflow: {
        k: [Operation::BitNot, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    byte_underflow_empty: {
        k: [Operation::Byte, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    byte_underflow_one: {
        k: [Operation::Byte, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    shift_left_underflow_empty: {
        k: [Operation::ShiftLeft, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    shift_left_underflow_one: {
        k: [Operation::ShiftLeft, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    shift_right_underflow_empty: {
        k: [Operation::ShiftRight, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    shift_right_underflow_one: {
        k: [Operation::ShiftRight, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    signed_shift_right_underflow_empty: {
        k: [Operation::SignedShiftRight, ..],
        word_stack: Stack::StackEmpty(),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackEmpty(),
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    signed_shift_right_underflow_one: {
        k: [Operation::SignedShiftRight, ..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: status,
    } => {
        k: [..],
        word_stack: Stack::StackCons(w0, Stack::StackEmpty()),
        status_code: Status::StackUnderflow(),
    }
    where w0: Int, status: StatusCode;

    stack_operation_underflow: {
        k: [GasResult::StackUnderflowResult(), ..],
        status_code: status,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    }
    where status: StatusCode;

    stack_operation_overflow: {
        k: [GasResult::StackOverflowResult(), ..],
        status_code: status,
    } => {
        k: [..],
        status_code: Status::StackOverflow(),
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

    static_mode_violation: {
        k: [GasResult::StaticViolationResult(), ..],
        status_code: status,
    } => {
        k: [..],
        status_code: Status::StaticModeViolation(),
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
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x02\x60\x03\x01\x58\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(0),
        CallState::gas: k::configuration::Cell(11),
        status_code: k::configuration::Cell(Status::Running()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x02\x60\x03\x01\x58\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackCons(5, Stack::StackCons(5, Stack::StackEmpty()))),
        CallState::pc: k::configuration::Cell(6),
        CallState::gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
        ..state
    }
}

/// All-path claim spanning the selected arithmetic and comparison tranches.
#[k::claim(all_paths, label = "arithmetic-comparison-tranches-stop")]
fn arithmetic_comparison_tranches_stop(
    k::cells! {
        k: k::configuration::KCell(ExecutionCommand::Run()),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x02\x60\x07\x05\x60\x02\x60\x07\x07\x60\x05\x60\x06\x60\x04\x08\x60\x05\x60\x06\x60\x04\x09\x60\x07\x60\x02\x10\x60\x02\x60\x07\x11\x60\x07\x60\x02\x12\x60\x02\x60\x07\x13\x60\x05\x60\x05\x14\x60\x00\x15\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(0),
        CallState::gas: k::configuration::Cell(107),
        status_code: k::configuration::Cell(Status::Running()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x02\x60\x07\x05\x60\x02\x60\x07\x07\x60\x05\x60\x06\x60\x04\x08\x60\x05\x60\x06\x60\x04\x09\x60\x07\x60\x02\x10\x60\x02\x60\x07\x11\x60\x07\x60\x02\x12\x60\x02\x60\x07\x13\x60\x05\x60\x05\x14\x60\x00\x15\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackCons(
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
        CallState::pc: k::configuration::Cell(52),
        CallState::gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
        ..state
    }
}

/// All-path claim spanning every Shanghai-active pure-word expression opcode.
#[k::claim(all_paths, label = "pure-word-tranche-stop")]
fn pure_word_tranche_stop(
    k::cells! {
        k: k::configuration::KCell(ExecutionCommand::Run()),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x08\x60\x02\x0a\x60\x80\x60\x00\x0b\x60\x0f\x60\x33\x16\x60\x0f\x60\x33\x17\x60\x0f\x60\x33\x18\x60\x00\x19\x61\xab\xcd\x60\x1e\x1a\x60\x03\x60\x04\x1b\x60\x80\x60\x03\x1c\x60\x00\x19\x60\x01\x1d\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(0),
        CallState::gas: k::configuration::Cell(149),
        status_code: k::configuration::Cell(Status::Running()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x08\x60\x02\x0a\x60\x80\x60\x00\x0b\x60\x0f\x60\x33\x16\x60\x0f\x60\x33\x17\x60\x0f\x60\x33\x18\x60\x00\x19\x61\xab\xcd\x60\x1e\x1a\x60\x03\x60\x04\x1b\x60\x80\x60\x03\x1c\x60\x00\x19\x60\x01\x1d\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackCons(
            115792089237316195423570985008687907853269984665640564039457584007913129639935,
            Stack::StackCons(
                16,
                Stack::StackCons(
                    48,
                    Stack::StackCons(
                        171,
                        Stack::StackCons(
                            115792089237316195423570985008687907853269984665640564039457584007913129639935,
                            Stack::StackCons(
                                60,
                                Stack::StackCons(
                                    63,
                                    Stack::StackCons(
                                        3,
                                        Stack::StackCons(
                                            115792089237316195423570985008687907853269984665640564039457584007913129639808,
                                            Stack::StackCons(256, Stack::StackEmpty()),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )),
        CallState::pc: k::configuration::Cell(50),
        CallState::gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
        ..state
    }
}

/// All-path claim spanning POP and depth-indexed DUP/SWAP execution.
#[k::claim(all_paths, label = "stack-manipulation-stop")]
fn stack_manipulation_stop(
    k::cells! {
        k: k::configuration::KCell(ExecutionCommand::Run()),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x01\x60\x02\x60\x03\x82\x91\x50\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(0),
        CallState::gas: k::configuration::Cell(17),
        status_code: k::configuration::Cell(Status::Running()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x01\x60\x02\x60\x03\x82\x91\x50\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackCons(
            3,
            Stack::StackCons(1, Stack::StackCons(1, Stack::StackEmpty())),
        )),
        CallState::pc: k::configuration::Cell(9),
        CallState::gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
        ..state
    }
}

/// All-path claim spanning false and true JUMPI, JUMP, and JUMPDEST execution.
#[k::claim(all_paths, label = "control-flow-tranche-stop")]
fn control_flow_tranche_stop(
    k::cells! {
        k: k::configuration::KCell(ExecutionCommand::Run()),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x00\x60\xff\x57\x60\x01\x60\x0d\x57\xfe\xfe\xfe\x5b\x60\x12\x56\xfe\x5b\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(0),
        CallState::gas: k::configuration::Cell(45),
        status_code: k::configuration::Cell(Status::Running()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x00\x60\xff\x57\x60\x01\x60\x0d\x57\xfe\xfe\xfe\x5b\x60\x12\x56\xfe\x5b\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(19),
        CallState::gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
        ..state
    }
}

/// All-path claim spanning Shanghai execution-context observations and block history.
#[k::claim(all_paths, label = "execution-context-tranche-stop")]
fn execution_context_tranche_stop(
    k::cells! {
        k: k::configuration::KCell(ExecutionCommand::Run()),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x30\x32\x33\x34\x36\x38\x3a\x3d\x41\x42\x43\x44\x45\x46\x48\x60\x10\x40\x5a\x00")),
        CallState::address: k::configuration::Cell(10),
        origin: k::configuration::Cell(11),
        CallState::caller: k::configuration::Cell(12),
        CallState::call_value: k::configuration::Cell(13),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"\xaa\xbb\xcc")),
        gas_price: k::configuration::Cell(14),
        output: k::configuration::Cell(k::bytes!(b"\xdd\xee")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::concat(
            list::item(99),
            list::concat(list::item(0), list::empty()),
        )),
        coinbase: k::configuration::Cell(15),
        timestamp: k::configuration::Cell(16),
        number: k::configuration::Cell(17),
        prev_randao: k::configuration::Cell(18),
        gas_limit: k::configuration::Cell(19),
        chain_id: k::configuration::Cell(20),
        base_fee: k::configuration::Cell(21),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(0),
        CallState::gas: k::configuration::Cell(55),
        status_code: k::configuration::Cell(Status::Running()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x30\x32\x33\x34\x36\x38\x3a\x3d\x41\x42\x43\x44\x45\x46\x48\x60\x10\x40\x5a\x00")),
        CallState::address: k::configuration::Cell(10),
        origin: k::configuration::Cell(11),
        CallState::caller: k::configuration::Cell(12),
        CallState::call_value: k::configuration::Cell(13),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"\xaa\xbb\xcc")),
        gas_price: k::configuration::Cell(14),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::concat(
            list::item(99),
            list::concat(list::item(0), list::empty()),
        )),
        coinbase: k::configuration::Cell(15),
        timestamp: k::configuration::Cell(16),
        number: k::configuration::Cell(17),
        prev_randao: k::configuration::Cell(18),
        gas_limit: k::configuration::Cell(19),
        chain_id: k::configuration::Cell(20),
        base_fee: k::configuration::Cell(21),
        CallState::word_stack: k::configuration::Cell(Stack::StackCons(
            0,
            Stack::StackCons(
                99,
                Stack::StackCons(
                    21,
                    Stack::StackCons(
                        20,
                        Stack::StackCons(
                            19,
                            Stack::StackCons(
                                18,
                                Stack::StackCons(
                                    17,
                                    Stack::StackCons(
                                        16,
                                        Stack::StackCons(
                                            15,
                                            Stack::StackCons(
                                                2,
                                                Stack::StackCons(
                                                    14,
                                                    Stack::StackCons(
                                                        20,
                                                        Stack::StackCons(
                                                            3,
                                                            Stack::StackCons(
                                                                13,
                                                                Stack::StackCons(
                                                                    12,
                                                                    Stack::StackCons(
                                                                        11,
                                                                        Stack::StackCons(
                                                                            10,
                                                                            Stack::StackEmpty(),
                                                                        ),
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )),
        CallState::pc: k::configuration::Cell(19),
        CallState::gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
        ..state
    }
}

/// All-path claim spanning memory writes, reads, size observation, and STOP.
#[k::claim(all_paths, label = "memory-tranche-stop")]
fn memory_tranche_stop(
    k::cells! {
        k: k::configuration::KCell(ExecutionCommand::Run()),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\xaa\x60\x00\x52\x60\x00\x51\x59\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"\xdd")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(0),
        CallState::gas: k::configuration::Cell(20),
        status_code: k::configuration::Cell(Status::Running()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\xaa\x60\x00\x52\x60\x00\x51\x59\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xaa")),
        CallState::memory_used: k::configuration::Cell(1),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackCons(32, Stack::StackCons(170, Stack::StackEmpty()))),
        CallState::pc: k::configuration::Cell(9),
        CallState::gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
        ..state
    }
}

/// All-path claim spanning calldata load and all selected byte-copy sources.
#[k::claim(all_paths, label = "load-copy-tranche-stop")]
fn load_copy_tranche_stop(
    k::cells! {
        k: k::configuration::KCell(ExecutionCommand::Run()),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x00\x35\x60\x03\x60\x01\x60\x00\x37\x60\x02\x60\x00\x60\x03\x39\x60\x02\x60\x01\x60\x05\x3e\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"\xaa\xbb\xcc\xdd")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"\x11\x22\x33")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"")),
        CallState::memory_used: k::configuration::Cell(0),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackEmpty()),
        CallState::pc: k::configuration::Cell(0),
        CallState::gas: k::configuration::Cell(54),
        status_code: k::configuration::Cell(Status::Running()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        CallState::program: k::configuration::Cell(k::bytes!(b"\x60\x00\x35\x60\x03\x60\x01\x60\x00\x37\x60\x02\x60\x00\x60\x03\x39\x60\x02\x60\x01\x60\x05\x3e\x00")),
        CallState::address: k::configuration::Cell(0),
        origin: k::configuration::Cell(0),
        CallState::caller: k::configuration::Cell(0),
        CallState::call_value: k::configuration::Cell(0),
        CallState::call_data: k::configuration::Cell(k::bytes!(b"\xaa\xbb\xcc\xdd")),
        gas_price: k::configuration::Cell(0),
        output: k::configuration::Cell(k::bytes!(b"")),
        CallState::local_mem: k::configuration::Cell(k::bytes!(b"\xbb\xcc\xdd\x60\x00\x22\x33\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00")),
        CallState::memory_used: k::configuration::Cell(1),
        block_hashes: k::configuration::Cell(list::empty()),
        coinbase: k::configuration::Cell(0),
        timestamp: k::configuration::Cell(0),
        number: k::configuration::Cell(0),
        prev_randao: k::configuration::Cell(0),
        gas_limit: k::configuration::Cell(0),
        chain_id: k::configuration::Cell(0),
        base_fee: k::configuration::Cell(0),
        CallState::word_stack: k::configuration::Cell(Stack::StackCons(
            77224998574671802608401215176576978315802517580781917942944813718736052682752,
            Stack::StackEmpty(),
        )),
        CallState::pc: k::configuration::Cell(24),
        CallState::gas: k::configuration::Cell(0),
        status_code: k::configuration::Cell(Status::Success()),
        ..state
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
        assert!(descriptors_json.contains(r#""application": "int_pow_mod""#));
        assert!(descriptors_json.contains(r#""application": "int_shift_left""#));
        assert!(descriptors_json.contains(r#""application": "int_bit_xor""#));
        assert!(semantic_json.contains(r#""application": "int_mod""#));
        assert!(semantic_json.contains(r#""application": "int_pow_mod""#));
        assert!(semantic_json.contains(r#""application": "int_shift_left""#));
        assert!(semantic_json.contains(r#""application": "int_bit_xor""#));
        assert!(definition_json.contains(r#""application": "int_mod""#));
        assert!(definition_json.contains(r#""application": "int_pow_mod""#));
        assert!(definition_json.contains(r#""application": "int_shift_left""#));
        assert!(definition_json.contains(r#""application": "int_bit_xor""#));
        assert!(source.source().contains(" modInt "));
        assert!(source.source().contains(" ^%Int "));
        assert!(source.source().contains(" <<Int "));
        assert!(source.source().contains(" xorInt "));
        assert!(source.source().contains("<wordStack>"));
        assert!(source.source().contains("EVMC_OUT_OF_GAS"));
        assert!(
            source
                .source()
                .contains("<account multiplicity=\"*\" type=\"Map\">")
        );
        let storage_load = source
            .source()
            .split("rule [begin-storage-load]:")
            .nth(1)
            .expect("storage-load rule is emitted")
            .split("rule [begin-storage-store]:")
            .next()
            .unwrap();
        assert!(storage_load.contains("\n    <account>"));
        assert!(storage_load.contains("\n        <acctID>"));
        assert!(storage_load.contains("\n        <storage>"));
        assert!(storage_load.contains("\n        ...\n    </account>"));
        assert!(storage_load.contains("\n    requires "));
        assert!(!storage_load.contains("\n    <acctID>"));
        assert!(!storage_load.contains("\n    <storage>"));
    }
}
