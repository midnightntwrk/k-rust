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
#[k::cons_list]
#[k::precedence((StackEmpty, StackCons))]
pub enum Stack {
    #[k::syntax(".WordStack")]
    StackEmpty(),
    #[k::syntax("{head} : {tail}")]
    StackCons { head: Int, tail: WordStack },
}

#[k::constructors(sort = LogEntry, result = k::KResult)]
pub enum LogRecord {
    #[k::syntax("logEntry({address}, {topics}, {data})")]
    Entry {
        address: Int,
        topics: List,
        data: Bytes,
    },
}

#[k::constructors(sort = G1Point, result = k::KResult)]
pub enum Bn128Point {
    #[k::syntax("({x}, {y})")]
    Point { x: Int, y: Int },
}

#[k::constructors(sort = G2Point, result = k::KResult)]
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
pub enum CopyResult {
    #[k::syntax("#returnDataCopyValid({remaining})")]
    ReturnDataCopyValid { remaining: Int },
    #[k::syntax("#returnDataCopyInvalid({remaining})")]
    ReturnDataCopyInvalid { remaining: Int },
}

#[k::constructors(sort = JumpStep, result = k::KResult)]
pub enum JumpResult {
    #[k::syntax("#jumpValid({destination})")]
    JumpValid { destination: Int },
    #[k::syntax("#jumpInvalid")]
    JumpInvalid(),
    #[k::syntax("#jumpFallthrough")]
    JumpFallthrough(),
}

#[k::constructors(sort = Command, result = k::KResult)]
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
pub enum SavedWorldState {
    #[k::syntax(
        "{{ {account_id}, {balance}, {code}, {nonce}, {storage}, {original_storage} | {self_destruct}, {logs}, {refund}, {accessed_accounts}, {accessed_storage}, {created_accounts} }}"
    )]
    Snapshot {
        account_id: Int,
        balance: Int,
        code: Bytes,
        nonce: Int,
        storage: Map<Int, Int>,
        original_storage: Map<Int, Int>,
        self_destruct: Set<Int>,
        logs: List<LogEntry>,
        refund: Int,
        accessed_accounts: Set<Int>,
        accessed_storage: Map<Int, Set<Int>>,
        created_accounts: Set<Int>,
    },
}

/// 2^256, the number of 256-bit words: word arithmetic is modulo it.
#[k::constant]
pub const POW256: Int =
    0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;

/// 2^255, the least word whose sign bit is set.
#[k::constant]
pub const POW255: Int =
    0x8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;

#[k::function(total, syntax = "#kevmChop({value})")]
pub fn Chop(value: k::Term<Int>) -> k::Term<Int> {
    int::rem_euclid(value, POW256)
}

#[k::function(total, syntax = "#kevmWordDiv({dividend}, {divisor})")]
pub fn WordDiv(dividend: k::Term<Int>, divisor: k::Term<Int>) -> k::Term<Int> {
    if divisor == 0 { 0 } else { dividend / divisor }
}

#[k::function(total, syntax = "#kevmWordMod({dividend}, {divisor})")]
pub fn WordMod(dividend: k::Term<Int>, divisor: k::Term<Int>) -> k::Term<Int> {
    if divisor == 0 {
        0
    } else {
        int::rem_euclid(dividend, divisor)
    }
}

#[k::function(total, syntax = "#kevmSign({value})")]
pub fn Sign(value: k::Term<Int>) -> k::Term<Int> {
    if 0 <= value && value < POW255 {
        1
    } else if POW255 <= value && value < POW256 {
        -1
    } else {
        0
    }
}

#[k::function(total, syntax = "#kevmAbs({value})")]
pub fn Magnitude(value: k::Term<Int>) -> k::Term<Int> {
    if 0 <= value && value < POW255 {
        value
    } else if POW255 <= value && value < POW256 {
        Chop(-value)
    } else {
        0
    }
}

#[k::function(partial, syntax = "#kevmSignedWordDiv({dividend}, {divisor})")]
pub fn SignedWordDiv(dividend: k::Term<Int>, divisor: k::Term<Int>) -> k::Term<Int> {
    match Sign(dividend) * Sign(divisor) {
        1 => WordDiv(Magnitude(dividend), Magnitude(divisor)),
        -1 => Chop(-WordDiv(Magnitude(dividend), Magnitude(divisor))),
    }
}

#[k::function(partial, syntax = "#kevmSignedWordMod({dividend}, {divisor})")]
pub fn SignedWordMod(dividend: k::Term<Int>, divisor: k::Term<Int>) -> k::Term<Int> {
    match Sign(dividend) {
        1 => WordMod(Magnitude(dividend), Magnitude(divisor)),
        -1 => Chop(-WordMod(Magnitude(dividend), Magnitude(divisor))),
    }
}

#[k::function(total, syntax = "#kevmBoolToWord({value})")]
pub fn BoolToWord(value: k::Term<Bool>) -> k::Term<Int>;

k::equations! {
    for BoolToWord;
    bool_to_word_true : true  => 1;
    bool_to_word_false: false => 0;
}

#[k::function(
    total,
    underspecified = "SLT and SGT apply it to stack words, so both operands are in 0..2^256",
    syntax = "#kevmSignedLess({left}, {right})"
)]
pub fn SignedLess(left: k::Term<Int>, right: k::Term<Int>) -> k::Term<Int> {
    match (Sign(left), Sign(right)) {
        (1, 1) => BoolToWord(left < right),
        (1, -1) => BoolToWord(false),
        (-1, 1) => BoolToWord(true),
        (-1, -1) => BoolToWord(Magnitude(right) < Magnitude(left)),
    }
}

#[k::function(total, syntax = "#kevmExpCost({exponent})")]
pub fn ExpCost(exponent: k::Term<Int>) -> k::Term<Int> {
    if exponent <= 0 {
        10
    } else {
        10 + 50 * (int::log2(exponent) / 8 + 1)
    }
}

#[k::function(total, syntax = "#kevmShiftLeft({value}, {shift})")]
pub fn WordShiftLeft(value: k::Term<Int>, shift: k::Term<Int>) -> k::Term<Int> {
    if value >= 0 && shift >= 0 && shift < 256 {
        Chop(value << shift)
    } else {
        0
    }
}

#[k::function(total, syntax = "#kevmShiftRight({value}, {shift})")]
pub fn WordShiftRight(value: k::Term<Int>, shift: k::Term<Int>) -> k::Term<Int> {
    if value >= 0 && shift >= 0 && shift < 256 {
        value >> shift
    } else {
        0
    }
}

#[k::function(total, syntax = "#kevmSignedShiftRight({value}, {shift})")]
pub fn WordSignedShiftRight(value: k::Term<Int>, shift: k::Term<Int>) -> k::Term<Int> {
    if value < 0 || shift < 0 {
        0
    } else if shift < 256 {
        Chop((Magnitude(value) * Sign(value)) >> shift)
    } else if Sign(value) == -1 {
        POW256 - 1
    } else {
        0
    }
}

#[k::function(total, syntax = "#kevmByte({index}, {value})")]
pub fn WordByte(index: k::Term<Int>, value: k::Term<Int>) -> k::Term<Int> {
    if index >= 0 && index < 32 {
        int::rem_euclid(value >> (8 * (31 - index)), 256)
    } else {
        0
    }
}

#[k::function(total, syntax = "#kevmSignExtend({index}, {value})")]
pub fn WordSignExtend(index: k::Term<Int>, value: k::Term<Int>) -> k::Term<Int> {
    if index < 0 || index >= 32 {
        value
    } else if SignExtendByte(index, value) < 128 {
        Chop(((1 << (8 * (index + 1))) - 1) & value)
    } else {
        Chop(((POW256 - 1) ^ ((1 << (8 * (index + 1))) - 1)) | value)
    }
}

/// Byte `index` of `value`, counting from the least significant byte.
#[k::requires(index >= 0)]
#[k::function(
    total,
    underspecified = "a byte position is never negative: WordSignExtend reads it only for 0 <= index < 32",
    syntax = "#kevmSignExtendByte({index}, {value})"
)]
pub fn SignExtendByte(index: k::Term<Int>, value: k::Term<Int>) -> k::Term<Int> {
    int::rem_euclid(value >> (8 * index), 256)
}

#[k::function(
    partial,
    syntax = "#kevmBlockHash({hashes}, {requested}, {highest}, {age})"
)]
pub fn BlockHashLookup(
    hashes: k::Term<List>,
    requested: k::Term<Int>,
    highest: k::Term<Int>,
    age: k::Term<Int>,
) -> k::Term<Int>;

k::equations! {
    for BlockHashLookup;
    #[k::requires(requested > highest)]
    block_hash_future       : (_, requested, highest, _)        => 0;
    #[k::requires(requested <= highest && age >= 256)]
    block_hash_too_old      : (_, requested, highest, age)      => 0;
    #[k::requires(bool::and(
        requested <= highest && age < 256,
        age < list::size(hashes) && list::get(hashes, age) == 0,
    ))]
    block_hash_zero_sentinel: (hashes, requested, highest, age) => 0;
    #[k::requires(bool::and(
        requested == highest && age < 256,
        age < list::size(hashes) && list::get(hashes, age) != 0,
    ))]
    block_hash_found        : (hashes, requested, highest, age) => list::get(hashes, age);
    #[k::requires(bool::and(
        requested < highest && age < 256,
        age < list::size(hashes) && list::get(hashes, age) != 0,
    ))]
    block_hash_continue:
        (hashes, requested, highest, age)
        => BlockHashLookup { hashes, requested, highest: highest - 1, age: age + 1 };
}

#[k::function(total, syntax = "#kevmMemoryUsageUpdate({used}, {start}, {width})")]
pub fn MemoryUsageUpdate(
    used: k::Term<Int>,
    start: k::Term<Int>,
    width: k::Term<Int>,
) -> k::Term<Int> {
    if width <= 0 {
        used
    } else if used >= (start + width + 31) / 32 {
        used
    } else {
        (start + width + 31) / 32
    }
}

#[k::function(total, syntax = "#kevmMemoryCost({words})")]
pub fn MemoryCost(words: k::Term<Int>) -> k::Term<Int> {
    3 * words + words * words / 512
}

#[k::function(total, syntax = "#kevmMemoryExpansionCost({used}, {start}, {width})")]
pub fn MemoryExpansionCost(
    used: k::Term<Int>,
    start: k::Term<Int>,
    width: k::Term<Int>,
) -> k::Term<Int> {
    MemoryCost(MemoryUsageUpdate { used, start, width }) - MemoryCost(used)
}

#[k::function(total, syntax = "#kevmCopyGasCost({used}, {start}, {width})")]
pub fn CopyGasCost(used: k::Term<Int>, start: k::Term<Int>, width: k::Term<Int>) -> k::Term<Int> {
    MemoryExpansionCost { used, start, width } + (3 + 3 * ((width + 31) / 32))
}

#[k::function(total, syntax = "#kevmAccountAccessCost({accessed}, {account})")]
pub fn AccountAccessCost(accessed: k::Term<Set>, account: k::Term<Int>) -> k::Term<Int> {
    if set::contains(account, accessed) {
        100
    } else {
        2600
    }
}

#[k::function(total, syntax = "#kevmAccountEmpty({code}, {nonce}, {balance})")]
pub fn AccountEmpty(
    code: k::Term<Bytes>,
    nonce: k::Term<Int>,
    balance: k::Term<Int>,
) -> k::Term<Bool> {
    bytes::length(code) == 0 && nonce == 0 && balance == 0
}

#[k::function(
    total,
    syntax = "#kevmCallMemoryUsage({used}, {argument_start}, {argument_width}, {return_start}, {return_width})"
)]
pub fn CallMemoryUsage(
    used: k::Term<Int>,
    argument_start: k::Term<Int>,
    argument_width: k::Term<Int>,
    return_start: k::Term<Int>,
    return_width: k::Term<Int>,
) -> k::Term<Int> {
    MemoryUsageUpdate {
        used: MemoryUsageUpdate {
            used,
            start: argument_start,
            width: argument_width,
        },
        start: return_start,
        width: return_width,
    }
}

#[k::function(
    total,
    syntax = "#kevmStaticCallCost({accessed}, {account}, {used}, {argument_start}, {argument_width}, {return_start}, {return_width})"
)]
pub fn StaticCallCost(
    accessed: k::Term<Set>,
    account: k::Term<Int>,
    used: k::Term<Int>,
    argument_start: k::Term<Int>,
    argument_width: k::Term<Int>,
    return_start: k::Term<Int>,
    return_width: k::Term<Int>,
) -> k::Term<Int> {
    AccountAccessCost { accessed, account }
        + (MemoryCost(CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        }) - MemoryCost(used))
}

#[k::function(total, syntax = "#kevmStaticCallGas({requested}, {available})")]
pub fn StaticCallGas(requested: k::Term<Int>, available: k::Term<Int>) -> k::Term<Int> {
    if requested <= available - available / 64 {
        requested
    } else {
        available - available / 64
    }
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

#[k::function(total, syntax = "#kevmEcrecOutput({public_key})")]
pub fn EcrecOutput(public_key: k::Term<Bytes>) -> k::Term<Bytes> {
    if bytes::length(public_key) <= 0 {
        bytes::empty()
    } else {
        CopyBytes {
            memory: bytes::pad_right(bytes::empty(), 32, 0),
            destination: 12,
            source: ReturnBytes(Keccak256Raw { value: public_key }, 12, 20),
            source_index: 0,
            remaining: 20,
        }
    }
}

/// secp256k1's group order n: ECREC recovers only signatures whose r and s lie in (0, n).
#[k::constant]
pub const SECP256K1_N: Int =
    0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fffe_baae_dce6_af48_a03b_bfd2_5e8c_d036_4141;

/// secp256k1's field prime p: the curve is y^2 = x^3 + 7 over the integers modulo p.
#[k::constant]
pub const SECP256K1_P: Int =
    0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_fffe_ffff_fc2f;

/// ECREC's recoverability: v is 27 or 28, 0 < r < n, 0 < s < n, and r is the x-coordinate of a
/// curve point.
///
/// Since r < n < p, r is a field element, and it is an x-coordinate exactly when r^3 + 7 is a
/// square modulo p. p is an odd prime, so by Euler's criterion a value a with p not dividing a is
/// a square exactly when a^((p - 1) / 2) is 1 modulo p (it is p - 1 otherwise). The case p | a
/// cannot occur: a root x of x^3 + 7 would give the point (x, 0), of order 2, and the group's
/// order n is odd. So the residue test below is exact. The modulus is the nonzero constant p, so
/// every operation applied here has a determined value.
#[k::function(total, syntax = "#kevmEcrecRecoverable({v}, {r}, {s})")]
pub fn EcrecRecoverable(v: k::Term<Int>, r: k::Term<Int>, s: k::Term<Int>) -> k::Term<Bool> {
    (v == 27 || v == 28)
        && 0 < r
        && r < SECP256K1_N
        && 0 < s
        && s < SECP256K1_N
        && int::pow_mod(r * r * r + 7, (SECP256K1_P - 1) / 2, SECP256K1_P) == 1
}

/// ECREC's output: the EVM's precompile yields the empty output on a signature that is not
/// recoverable, so the ECDSA hook is applied only to a recoverable one.
#[k::function(total, syntax = "#kevmEcrecPrecompileOutput({data})")]
pub fn EcrecPrecompileOutput(data: k::Term<Bytes>) -> k::Term<Bytes> {
    if EcrecRecoverable(
        BytesToInt(ReturnBytes(data, 32, 32), 0, 0),
        BytesToInt(ReturnBytes(data, 64, 32), 0, 0),
        BytesToInt(ReturnBytes(data, 96, 32), 0, 0),
    ) {
        EcrecOutput {
            public_key: EcdsaRecover {
                hash: ReturnBytes(data, 0, 32),
                recovery: BytesToInt(ReturnBytes(data, 32, 32), 0, 0),
                r: ReturnBytes(data, 64, 32),
                s: ReturnBytes(data, 96, 32),
            },
        }
    } else {
        bytes::empty()
    }
}

#[k::function(
    total,
    syntax = "#kevmResolveEcrecPrecompile({requested}, {available})"
)]
pub fn ResolveEcrecPrecompile(
    requested: k::Term<Int>,
    available: k::Term<Int>,
) -> k::Term<PrecompileStep> {
    if StaticCallGas(requested, available) >= 3000 {
        PrecompileResult::EcrecPrecompileSuccess {
            remaining: available - 3000,
        }
    } else {
        PrecompileResult::EcrecPrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    }
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

#[k::function(total, syntax = "#kevmSha256PrecompileCost({data})")]
pub fn Sha256PrecompileCost(data: k::Term<Bytes>) -> k::Term<Int> {
    60 + 12 * ((bytes::length(data) + 31) / 32)
}

#[k::function(
    total,
    syntax = "#kevmResolveSha256Precompile({data}, {requested}, {available})"
)]
pub fn ResolveSha256Precompile(
    data: k::Term<Bytes>,
    requested: k::Term<Int>,
    available: k::Term<Int>,
) -> k::Term<PrecompileStep> {
    if StaticCallGas(requested, available) >= Sha256PrecompileCost(data) {
        PrecompileResult::Sha256PrecompileSuccess {
            remaining: available - Sha256PrecompileCost(data),
        }
    } else {
        PrecompileResult::Sha256PrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    }
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

#[k::function(total, syntax = "#kevmRipemd160PrecompileCost({data})")]
pub fn Ripemd160PrecompileCost(data: k::Term<Bytes>) -> k::Term<Int> {
    600 + 120 * ((bytes::length(data) + 31) / 32)
}

#[k::function(
    total,
    syntax = "#kevmResolveRipemd160Precompile({data}, {requested}, {available})"
)]
pub fn ResolveRipemd160Precompile(
    data: k::Term<Bytes>,
    requested: k::Term<Int>,
    available: k::Term<Int>,
) -> k::Term<PrecompileStep> {
    if StaticCallGas(requested, available) >= Ripemd160PrecompileCost(data) {
        PrecompileResult::Ripemd160PrecompileSuccess {
            remaining: available - Ripemd160PrecompileCost(data),
        }
    } else {
        PrecompileResult::Ripemd160PrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    }
}

#[k::function(total, syntax = "#kevmIdentityPrecompileCost({data})")]
pub fn IdentityPrecompileCost(data: k::Term<Bytes>) -> k::Term<Int> {
    15 + 3 * ((bytes::length(data) + 31) / 32)
}

#[k::function(
    total,
    syntax = "#kevmResolveIdentityPrecompile({data}, {requested}, {available})"
)]
pub fn ResolveIdentityPrecompile(
    data: k::Term<Bytes>,
    requested: k::Term<Int>,
    available: k::Term<Int>,
) -> k::Term<PrecompileStep> {
    if StaticCallGas(requested, available) >= IdentityPrecompileCost(data) {
        PrecompileResult::IdentityPrecompileSuccess {
            remaining: available - IdentityPrecompileCost(data),
        }
    } else {
        PrecompileResult::IdentityPrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    }
}

#[k::function(total, syntax = "#kevmModExpPrecompileCost({data})")]
pub fn ModExpPrecompileCost(data: k::Term<Bytes>) -> k::Term<Int> {
    Maximum(
        200,
        (Maximum(
            BytesToInt(ReturnBytes(data, 0, 32), 0, 0),
            BytesToInt(ReturnBytes(data, 64, 32), 0, 0),
        ) + 7)
            / 8
            * ((Maximum(
                BytesToInt(ReturnBytes(data, 0, 32), 0, 0),
                BytesToInt(ReturnBytes(data, 64, 32), 0, 0),
            ) + 7)
                / 8)
            * Maximum(
                ModExpAdjustedExponentLength {
                    data,
                    base_length: BytesToInt(ReturnBytes(data, 0, 32), 0, 0),
                    exponent_length: BytesToInt(ReturnBytes(data, 32, 32), 0, 0),
                },
                1,
            )
            / 3,
    )
}

#[k::function(
    total,
    syntax = "#kevmModExpAdjustedExponentLength({data}, {base_length}, {exponent_length})"
)]
pub fn ModExpAdjustedExponentLength(
    data: k::Term<Bytes>,
    base_length: k::Term<Int>,
    exponent_length: k::Term<Int>,
) -> k::Term<Int> {
    if exponent_length <= 32 {
        ModExpExponentHeadBits(BytesToInt(
            ReturnBytes(data, 96 + base_length, exponent_length),
            0,
            0,
        ))
    } else {
        8 * (exponent_length - 32)
            + ModExpExponentHeadBits(BytesToInt(ReturnBytes(data, 96 + base_length, 32), 0, 0))
    }
}

#[k::function(total, syntax = "#kevmModExpExponentHeadBits({value})")]
pub fn ModExpExponentHeadBits(value: k::Term<Int>) -> k::Term<Int> {
    if value <= 1 { 0 } else { int::log2(value) }
}

#[k::function(total, syntax = "#kevmModExpPrecompileOutput({data})")]
pub fn ModExpPrecompileOutput(data: k::Term<Bytes>) -> k::Term<Bytes> {
    ModExpOutputBody {
        body: ReturnBytes(data, 96, Maximum(0, bytes::length(data) - 96)),
        base_length: BytesToInt(ReturnBytes(data, 0, 32), 0, 0),
        exponent_length: BytesToInt(ReturnBytes(data, 32, 32), 0, 0),
        modulus_length: BytesToInt(ReturnBytes(data, 64, 32), 0, 0),
    }
}

#[k::function(
    total,
    syntax = "#kevmModExpOutputBody({body}, {base_length}, {exponent_length}, {modulus_length})"
)]
pub fn ModExpOutputBody(
    body: k::Term<Bytes>,
    base_length: k::Term<Int>,
    exponent_length: k::Term<Int>,
    modulus_length: k::Term<Int>,
) -> k::Term<Bytes> {
    if modulus_length <= 0 {
        bytes::empty()
    } else {
        ModExpOutputExponent {
            body: ReturnBytes(
                body,
                base_length,
                Maximum(0, bytes::length(body) - base_length),
            ),
            base: BytesToInt(ReturnBytes(body, 0, base_length), 0, 0),
            exponent_length,
            modulus_length,
        }
    }
}

#[k::function(
    total,
    syntax = "#kevmModExpOutputExponent({body}, {base}, {exponent_length}, {modulus_length})"
)]
pub fn ModExpOutputExponent(
    body: k::Term<Bytes>,
    base: k::Term<Int>,
    exponent_length: k::Term<Int>,
    modulus_length: k::Term<Int>,
) -> k::Term<Bytes> {
    WriteMemoryWord {
        memory: bytes::pad_right(bytes::empty(), modulus_length, 0),
        index: 0,
        remaining: modulus_length,
        value: ModExpPower {
            base,
            exponent: BytesToInt(ReturnBytes(body, 0, exponent_length), 0, 0),
            modulus: BytesToInt(ReturnBytes(body, exponent_length, modulus_length), 0, 0),
        },
    }
}

#[k::function(total, syntax = "#kevmModExpPower({base}, {exponent}, {modulus})")]
pub fn ModExpPower(
    base: k::Term<Int>,
    exponent: k::Term<Int>,
    modulus: k::Term<Int>,
) -> k::Term<Int> {
    if modulus <= 0 {
        0
    } else {
        int::pow_mod(base, exponent, modulus)
    }
}

#[k::function(
    total,
    syntax = "#kevmResolveModExpPrecompile({data}, {requested}, {available})"
)]
pub fn ResolveModExpPrecompile(
    data: k::Term<Bytes>,
    requested: k::Term<Int>,
    available: k::Term<Int>,
) -> k::Term<PrecompileStep> {
    if StaticCallGas(requested, available) >= ModExpPrecompileCost(data) {
        PrecompileResult::ModExpPrecompileSuccess {
            remaining: available - ModExpPrecompileCost(data),
        }
    } else {
        PrecompileResult::ModExpPrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    }
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

#[k::function(total, syntax = "#kevmEcAddFirstPoint({data})")]
pub fn EcAddFirstPoint(data: k::Term<Bytes>) -> k::Term<G1Point> {
    Bn128Point::Point {
        x: BytesToInt(ReturnBytes(data, 0, 32), 0, 0),
        y: BytesToInt(ReturnBytes(data, 32, 32), 0, 0),
    }
}

#[k::function(total, syntax = "#kevmEcAddSecondPoint({data})")]
pub fn EcAddSecondPoint(data: k::Term<Bytes>) -> k::Term<G1Point> {
    Bn128Point::Point {
        x: BytesToInt(ReturnBytes(data, 64, 32), 0, 0),
        y: BytesToInt(ReturnBytes(data, 96, 32), 0, 0),
    }
}

#[k::function(total, syntax = "#kevmBn128PointBytes({point})")]
pub fn Bn128PointBytes(point: k::Term<G1Point>) -> k::Term<Bytes>;

k::equations! {
    for Bn128PointBytes;
    bn128_point_bytes:
        Bn128Point::Point { x, y } => WriteMemoryWord {
            memory: WriteMemoryWord {
                memory: bytes::pad_right(bytes::empty(), 64, 0),
                index: 0,
                remaining: 32,
                value: x,
            },
            index: 32,
            remaining: 32,
            value: y,
        };
}

#[k::function(total, syntax = "#kevmEcAddPrecompileOutput({data})")]
pub fn EcAddPrecompileOutput(data: k::Term<Bytes>) -> k::Term<Bytes> {
    Bn128PointBytes {
        point: Bn128Add {
            left: EcAddFirstPoint { data },
            right: EcAddSecondPoint { data },
        },
    }
}

#[k::function(
    total,
    syntax = "#kevmResolveEcAddPrecompile({data}, {requested}, {available})"
)]
pub fn ResolveEcAddPrecompile(
    data: k::Term<Bytes>,
    requested: k::Term<Int>,
    available: k::Term<Int>,
) -> k::Term<PrecompileStep> {
    if StaticCallGas(requested, available) < 150 {
        PrecompileResult::EcAddPrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    } else if Bn128PointValid(EcAddFirstPoint(data)) {
        if Bn128PointValid(EcAddSecondPoint(data)) {
            PrecompileResult::EcAddPrecompileSuccess {
                remaining: available - 150,
            }
        } else {
            PrecompileResult::EcAddPrecompileFailure {
                remaining: available - StaticCallGas(requested, available),
            }
        }
    } else {
        PrecompileResult::EcAddPrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    }
}

#[k::function(total, syntax = "#kevmEcMulPoint({data})")]
pub fn EcMulPoint(data: k::Term<Bytes>) -> k::Term<G1Point> {
    Bn128Point::Point {
        x: BytesToInt(ReturnBytes(data, 0, 32), 0, 0),
        y: BytesToInt(ReturnBytes(data, 32, 32), 0, 0),
    }
}

#[k::function(total, syntax = "#kevmEcMulScalar({data})")]
pub fn EcMulScalar(data: k::Term<Bytes>) -> k::Term<Int> {
    BytesToInt(ReturnBytes(data, 64, 32), 0, 0)
}

#[k::function(total, syntax = "#kevmEcMulPrecompileOutput({data})")]
pub fn EcMulPrecompileOutput(data: k::Term<Bytes>) -> k::Term<Bytes> {
    Bn128PointBytes {
        point: Bn128Mul {
            point: EcMulPoint { data },
            scalar: EcMulScalar { data },
        },
    }
}

#[k::function(
    total,
    syntax = "#kevmResolveEcMulPrecompile({data}, {requested}, {available})"
)]
pub fn ResolveEcMulPrecompile(
    data: k::Term<Bytes>,
    requested: k::Term<Int>,
    available: k::Term<Int>,
) -> k::Term<PrecompileStep> {
    if StaticCallGas(requested, available) < 6000 {
        PrecompileResult::EcMulPrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    } else if Bn128PointValid(EcMulPoint(data)) {
        PrecompileResult::EcMulPrecompileSuccess {
            remaining: available - 6000,
        }
    } else {
        PrecompileResult::EcMulPrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    }
}

#[k::function(total, syntax = "#kevmEcPairingPrecompileCost({data})")]
pub fn EcPairingPrecompileCost(data: k::Term<Bytes>) -> k::Term<Int> {
    45000 + 34000 * (bytes::length(data) / 192)
}

#[k::function(total, syntax = "#kevmEcPairingG1Point({data}, {index})")]
pub fn EcPairingG1Point(data: k::Term<Bytes>, index: k::Term<Int>) -> k::Term<G1Point> {
    Bn128Point::Point {
        x: BytesToInt(ReturnBytes(data, index, 32), 0, 0),
        y: BytesToInt(ReturnBytes(data, index + 32, 32), 0, 0),
    }
}

#[k::function(total, syntax = "#kevmEcPairingG2Point({data}, {index})")]
pub fn EcPairingG2Point(data: k::Term<Bytes>, index: k::Term<Int>) -> k::Term<G2Point> {
    Bn128G2Point::G2 {
        x_real: BytesToInt(ReturnBytes(data, index + 96, 32), 0, 0),
        x_imaginary: BytesToInt(ReturnBytes(data, index + 64, 32), 0, 0),
        y_real: BytesToInt(ReturnBytes(data, index + 160, 32), 0, 0),
        y_imaginary: BytesToInt(ReturnBytes(data, index + 128, 32), 0, 0),
    }
}

#[k::function(total, syntax = "#kevmEcPairingG1Points({data}, {index}, {length})")]
pub fn EcPairingG1Points(
    data: k::Term<Bytes>,
    index: k::Term<Int>,
    length: k::Term<Int>,
) -> k::Term<List> {
    if index >= length {
        []
    } else {
        [
            EcPairingG1Point { data, index },
            ..EcPairingG1Points {
                data,
                index: index + 192,
                length,
            },
        ]
    }
}

#[k::function(total, syntax = "#kevmEcPairingG2Points({data}, {index}, {length})")]
pub fn EcPairingG2Points(
    data: k::Term<Bytes>,
    index: k::Term<Int>,
    length: k::Term<Int>,
) -> k::Term<List> {
    if index >= length {
        []
    } else {
        [
            EcPairingG2Point { data, index },
            ..EcPairingG2Points {
                data,
                index: index + 192,
                length,
            },
        ]
    }
}

#[k::function(total, syntax = "#kevmEcPairingPointsValid({data}, {index}, {length})")]
pub fn EcPairingPointsValid(
    data: k::Term<Bytes>,
    index: k::Term<Int>,
    length: k::Term<Int>,
) -> k::Term<Bool> {
    if index >= length {
        true
    } else {
        Bn128PointValid {
            point: EcPairingG1Point { data, index },
        } && Bn128G2PointValid {
            point: EcPairingG2Point { data, index },
        } && EcPairingPointsValid {
            data,
            index: index + 192,
            length,
        }
    }
}

#[k::function(total, syntax = "#kevmEcPairingPrecompileOutput({data})")]
pub fn EcPairingPrecompileOutput(data: k::Term<Bytes>) -> k::Term<Bytes> {
    WriteMemoryWord {
        memory: bytes::pad_right(bytes::empty(), 32, 0),
        index: 0,
        remaining: 32,
        value: BoolToWord(Bn128Ate {
            g1_points: EcPairingG1Points {
                data,
                index: 0,
                length: bytes::length(data),
            },
            g2_points: EcPairingG2Points {
                data,
                index: 0,
                length: bytes::length(data),
            },
        }),
    }
}

#[k::function(
    total,
    syntax = "#kevmResolveEcPairingPrecompile({data}, {requested}, {available})"
)]
pub fn ResolveEcPairingPrecompile(
    data: k::Term<Bytes>,
    requested: k::Term<Int>,
    available: k::Term<Int>,
) -> k::Term<PrecompileStep> {
    if StaticCallGas(requested, available) < EcPairingPrecompileCost(data) {
        PrecompileResult::EcPairingPrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    } else if int::rem_euclid(bytes::length(data), 192) == 0 {
        if EcPairingPointsValid(data, 0, bytes::length(data)) {
            PrecompileResult::EcPairingPrecompileSuccess {
                remaining: available - EcPairingPrecompileCost(data),
            }
        } else {
            PrecompileResult::EcPairingPrecompileFailure {
                remaining: available - StaticCallGas(requested, available),
            }
        }
    } else {
        PrecompileResult::EcPairingPrecompileFailure {
            remaining: available - StaticCallGas(requested, available),
        }
    }
}

#[k::function(total, syntax = "#kevmMinimum({left}, {right})")]
pub fn Minimum(left: k::Term<Int>, right: k::Term<Int>) -> k::Term<Int> {
    if left <= right { left } else { right }
}

#[k::function(total, syntax = "#kevmMaximum({left}, {right})")]
pub fn Maximum(left: k::Term<Int>, right: k::Term<Int>) -> k::Term<Int> {
    if left >= right { left } else { right }
}

#[k::function(total, syntax = "#kevmMarkAccountAccess({accessed}, {account})")]
pub fn MarkAccountAccess(accessed: k::Term<Set<Int>>, account: k::Term<Int>) -> k::Term<Set<Int>> {
    set::union(accessed, set::item(account))
}

#[k::function(
    total,
    syntax = "#kevmExternalCopyGasCost({accessed}, {account}, {used}, {start}, {width})"
)]
pub fn ExternalCopyGasCost(
    accessed: k::Term<Set>,
    account: k::Term<Int>,
    used: k::Term<Int>,
    start: k::Term<Int>,
    width: k::Term<Int>,
) -> k::Term<Int> {
    AccountAccessCost { accessed, account }
        + (MemoryExpansionCost { used, start, width } + 3 * ((width + 31) / 32))
}

#[k::function(
    total,
    syntax = "#kevmPrepareCopyMemory({memory}, {used}, {start}, {width})"
)]
pub fn PrepareCopyMemory(
    memory: k::Term<Bytes>,
    used: k::Term<Int>,
    start: k::Term<Int>,
    width: k::Term<Int>,
) -> k::Term<Bytes> {
    if width <= 0 {
        memory
    } else {
        bytes::pad_right(memory, MemoryUsageUpdate { used, start, width } * 32, 0)
    }
}

#[k::function(total, syntax = "#kevmMemoryByte({memory}, {index})")]
pub fn MemoryByte(memory: k::Term<Bytes>, index: k::Term<Int>) -> k::Term<Int> {
    if index >= 0 && index < bytes::length(memory) {
        bytes::get(memory, index)
    } else {
        0
    }
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

#[k::function(total, syntax = "#kevmBytesToInt({value}, {index}, {result})")]
pub fn BytesToInt(
    value: k::Term<Bytes>,
    index: k::Term<Int>,
    result: k::Term<Int>,
) -> k::Term<Int> {
    if index >= 0 && index < bytes::length(value) {
        BytesToInt(value, index + 1, result * 256 + bytes::get(value, index))
    } else {
        result
    }
}

#[k::function(total, syntax = "#kevmKeccak({value})")]
pub fn Keccak(value: k::Term<Bytes>) -> k::Term<Int> {
    BytesToInt(Keccak256Raw(value), 0, 0)
}

#[k::function(total, syntax = "#kevmStorageValue({storage}, {index})")]
pub fn StorageValue(storage: k::Term<Map>, index: k::Term<Int>) -> k::Term<Int> {
    if map::in_keys(index, storage) {
        map::get(storage, index)
    } else {
        0
    }
}

#[k::function(total, syntax = "#kevmStorageWarm({accessed}, {account}, {index})")]
pub fn StorageWarm(
    accessed: k::Term<Map>,
    account: k::Term<Int>,
    index: k::Term<Int>,
) -> k::Term<Bool> {
    if map::in_keys(account, accessed) {
        set::contains(index, map::get(accessed, account))
    } else {
        false
    }
}

#[k::function(
    total,
    syntax = "#kevmMarkStorageAccess({accessed}, {account}, {index})"
)]
pub fn MarkStorageAccess(
    accessed: k::Term<Map<Int, Set<Int>>>,
    account: k::Term<Int>,
    index: k::Term<Int>,
) -> k::Term<Map<Int, Set<Int>>> {
    if map::in_keys(account, accessed) {
        map::update(
            accessed,
            account,
            set::union(map::get(accessed, account), set::item(index)),
        )
    } else {
        map::update(accessed, account, set::item(index))
    }
}

#[k::function(total, syntax = "#kevmColdStorageSurcharge({warm})")]
pub fn ColdStorageSurcharge(warm: k::Term<Bool>) -> k::Term<Int>;

k::equations! {
    for ColdStorageSurcharge;
    cold_storage_surcharge_warm: true  => 0;
    cold_storage_surcharge_cold: false => 2100;
}

#[k::function(total, syntax = "#kevmStorageLoadCost({warm})")]
pub fn StorageLoadCost(warm: k::Term<Bool>) -> k::Term<Int>;

k::equations! {
    for StorageLoadCost;
    storage_load_cost_warm: true  => 100;
    storage_load_cost_cold: false => 2100;
}

#[k::function(
    total,
    syntax = "#kevmStorageStoreCost({original}, {current}, {new}, {warm})"
)]
pub fn StorageStoreCost(
    original: k::Term<Int>,
    current: k::Term<Int>,
    new: k::Term<Int>,
    warm: k::Term<Bool>,
) -> k::Term<Int> {
    if current == new {
        100 + ColdStorageSurcharge(warm)
    } else if original == current {
        if original == 0 {
            20000 + ColdStorageSurcharge(warm)
        } else {
            2900 + ColdStorageSurcharge(warm)
        }
    } else {
        100 + ColdStorageSurcharge(warm)
    }
}

#[k::function(
    total,
    syntax = "#kevmStorageRefundDelta({original}, {current}, {new})"
)]
pub fn StorageRefundDelta(
    original: k::Term<Int>,
    current: k::Term<Int>,
    new: k::Term<Int>,
) -> k::Term<Int> {
    if current == new {
        0
    } else if original == current {
        if original != 0 && new == 0 { 4800 } else { 0 }
    } else if original == 0 {
        if new == original { 19900 } else { 0 }
    } else if current == 0 {
        if new == original { -2000 } else { -4800 }
    } else if new == 0 {
        4800
    } else if new == original {
        2800
    } else {
        0
    }
}

#[k::function(
    total,
    syntax = "#kevmPrepareStorageStore({gas}, {original}, {current}, {new}, {warm}, {static_mode})"
)]
pub fn PrepareStorageStore(
    gas: k::Term<Int>,
    original: k::Term<Int>,
    current: k::Term<Int>,
    new: k::Term<Int>,
    warm: k::Term<Bool>,
    static_mode: k::Term<Bool>,
) -> k::Term<GasStep> {
    match static_mode {
        true => GasResult::StaticViolationResult(),
        false => {
            if gas <= 2300 {
                GasResult::InsufficientGas()
            } else {
                ChargeFixed {
                    op: Operation::StorageStore,
                    gas,
                    cost: StorageStoreCost {
                        original,
                        current,
                        new,
                        warm,
                    },
                }
            }
        }
    }
}

#[k::function(
    total,
    syntax = "#kevmReadMemoryWord({memory}, {index}, {remaining}, {value})"
)]
pub fn ReadMemoryWord(
    memory: k::Term<Bytes>,
    index: k::Term<Int>,
    remaining: k::Term<Int>,
    value: k::Term<Int>,
) -> k::Term<Int> {
    if remaining <= 0 {
        value
    } else {
        ReadMemoryWord {
            memory,
            index: index + 1,
            remaining: remaining - 1,
            value: value * 256 + MemoryByte(memory, index),
        }
    }
}

#[k::function(
    partial,
    syntax = "#kevmWriteMemoryWord({memory}, {index}, {remaining}, {value})"
)]
pub fn WriteMemoryWord(
    memory: k::Term<Bytes>,
    index: k::Term<Int>,
    remaining: k::Term<Int>,
    value: k::Term<Int>,
) -> k::Term<Bytes> {
    if remaining <= 0 {
        memory
    } else {
        WriteMemoryWord {
            memory: bytes::update(memory, index + (remaining - 1), int::rem_euclid(value, 256)),
            index,
            remaining: remaining - 1,
            value: value / 256,
        }
    }
}

#[k::function(
    partial,
    syntax = "#kevmCopyBytes({memory}, {destination}, {source}, {source_index}, {remaining})"
)]
pub fn CopyBytes(
    memory: k::Term<Bytes>,
    destination: k::Term<Int>,
    source: k::Term<Bytes>,
    source_index: k::Term<Int>,
    remaining: k::Term<Int>,
) -> k::Term<Bytes> {
    if remaining <= 0 {
        memory
    } else {
        CopyBytes {
            memory: bytes::update(memory, destination, MemoryByte(source, source_index)),
            destination: destination + 1,
            source,
            source_index: source_index + 1,
            remaining: remaining - 1,
        }
    }
}

#[k::function(total, syntax = "#kevmReturnBytes({memory}, {start}, {width})")]
pub fn ReturnBytes(
    memory: k::Term<Bytes>,
    start: k::Term<Int>,
    width: k::Term<Int>,
) -> k::Term<Bytes> {
    CopyBytes {
        memory: bytes::pad_right(bytes::empty(), width, 0),
        destination: 0,
        source: memory,
        source_index: start,
        remaining: width,
    }
}

#[k::function(
    total,
    syntax = "#kevmResolveReturnDataCopy({output}, {source_index}, {width}, {remaining})"
)]
pub fn ResolveReturnDataCopy(
    output: k::Term<Bytes>,
    source_index: k::Term<Int>,
    width: k::Term<Int>,
    remaining: k::Term<Int>,
) -> k::Term<CopyStep> {
    if source_index + width <= bytes::length(output) {
        CopyResult::ReturnDataCopyValid { remaining }
    } else {
        CopyResult::ReturnDataCopyInvalid { remaining }
    }
}

#[k::function(total, syntax = "#kevmStackSize({stack})")]
pub fn StackSize(stack: k::Term<WordStack>) -> k::Term<Int> {
    match stack {
        [] => 0,
        [_, tail @ ..] => 1 + StackSize(tail),
    }
}

#[k::function(partial, syntax = "#kevmStackAt({stack}, {index})")]
pub fn StackAt(stack: k::Term<WordStack>, index: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for StackAt;
    #[k::requires(index <= 0)]
    stack_at_here : ([head, ..], index)     => head;
    #[k::requires(index > 0)]
    stack_at_later: ([_, tail @ ..], index) => StackAt(tail, index - 1);
}

#[k::function(partial, syntax = "#kevmStackSet({stack}, {index}, {value})")]
pub fn StackSet(
    stack: k::Term<WordStack>,
    index: k::Term<Int>,
    value: k::Term<Int>,
) -> k::Term<WordStack>;

k::equations! {
    for StackSet;
    #[k::requires(index <= 0)]
    stack_set_here: ([_, tail @ ..], index, value) => [value, ..tail];
    #[k::requires(index > 0)]
    stack_set_later:
        ([head, tail @ ..], index, value) => [head, ..StackSet(tail, index - 1, value)];
}

#[k::function(total, syntax = "#kevmStackTakeList({stack}, {remaining})")]
pub fn StackTakeList(stack: k::Term<WordStack>, remaining: k::Term<Int>) -> k::Term<List> {
    if remaining <= 0 {
        []
    } else {
        match stack {
            [] => [0, ..StackTakeList([], remaining - 1)],
            [head, tail @ ..] => [head, ..StackTakeList(tail, remaining - 1)],
        }
    }
}

#[k::function(total, syntax = "#kevmStackDrop({stack}, {remaining})")]
pub fn StackDrop(stack: k::Term<WordStack>, remaining: k::Term<Int>) -> k::Term<WordStack> {
    if remaining <= 0 {
        stack
    } else {
        match stack {
            [] => [],
            [_, tail @ ..] => StackDrop(tail, remaining - 1),
        }
    }
}

#[k::function(partial, syntax = "#kevmPrepareStack({op}, {stack}, {gas})")]
pub fn PrepareStack(
    op: k::Term<OpCode>,
    stack: k::Term<WordStack>,
    gas: k::Term<Int>,
) -> k::Term<GasStep> {
    match op {
        Operation::Pop => {
            if StackSize(stack) == 0 {
                GasResult::StackUnderflowResult()
            } else {
                ChargeFixed {
                    op: Operation::Pop,
                    gas,
                    cost: 2,
                }
            }
        }
        Operation::Duplicate { depth } => {
            if StackSize(stack) < depth {
                GasResult::StackUnderflowResult()
            } else if StackSize(stack) < 1024 {
                ChargeFixed {
                    op: Operation::Duplicate { depth },
                    gas,
                    cost: 3,
                }
            } else {
                GasResult::StackOverflowResult()
            }
        }
        Operation::Swap { depth } => {
            if StackSize(stack) < depth + 1 {
                GasResult::StackUnderflowResult()
            } else {
                ChargeFixed {
                    op: Operation::Swap { depth },
                    gas,
                    cost: 3,
                }
            }
        }
    }
}

#[k::function(total, syntax = "#kevmPreparePush({op}, {stack}, {gas}, {cost})")]
pub fn PreparePush(
    op: k::Term<OpCode>,
    stack: k::Term<WordStack>,
    gas: k::Term<Int>,
    cost: k::Term<Int>,
) -> k::Term<GasStep> {
    if StackSize(stack) < 1024 {
        ChargeFixed { op, gas, cost }
    } else {
        GasResult::StackOverflowResult()
    }
}

#[k::function(
    total,
    syntax = "#kevmPrepareLog({topics}, {stack}, {gas}, {used}, {static_mode})"
)]
pub fn PrepareLog(
    topics: k::Term<Int>,
    stack: k::Term<WordStack>,
    gas: k::Term<Int>,
    used: k::Term<Int>,
    static_mode: k::Term<Bool>,
) -> k::Term<GasStep> {
    if StackSize(stack) < topics + 2 {
        GasResult::StackUnderflowResult()
    } else {
        match static_mode {
            true => GasResult::StaticViolationResult(),
            false => ChargeFixed {
                op: Operation::LogOpcode { topics },
                gas,
                cost: MemoryExpansionCost {
                    used,
                    start: StackAt { stack, index: 0 },
                    width: StackAt { stack, index: 1 },
                } + (375 + (8 * StackAt { stack, index: 1 } + 375 * topics)),
            },
        }
    }
}

#[k::function(
    total,
    syntax = "#kevmPrepareStaticCall({stack}, {accessed}, {used}, {gas})"
)]
pub fn PrepareStaticCall(
    stack: k::Term<WordStack>,
    accessed: k::Term<Set>,
    used: k::Term<Int>,
    gas: k::Term<Int>,
) -> k::Term<GasStep> {
    if StackSize(stack) < 6 {
        GasResult::StackUnderflowResult()
    } else {
        ChargeStaticCall {
            gas,
            cost: StaticCallCost {
                accessed,
                account: StackAt { stack, index: 1 },
                used,
                argument_start: StackAt { stack, index: 2 },
                argument_width: StackAt { stack, index: 3 },
                return_start: StackAt { stack, index: 4 },
                return_width: StackAt { stack, index: 5 },
            },
            account: StackAt { stack, index: 1 },
        }
    }
}

#[k::function(total, syntax = "#kevmChargeFixed({op}, {gas}, {cost})")]
pub fn ChargeFixed(op: k::Term<OpCode>, gas: k::Term<Int>, cost: k::Term<Int>) -> k::Term<GasStep> {
    if gas >= cost {
        GasResult::EnoughGas {
            op,
            remaining: gas - cost,
        }
    } else {
        GasResult::InsufficientGas()
    }
}

#[k::function(total, syntax = "#kevmChargeStaticCall({gas}, {cost}, {account})")]
pub fn ChargeStaticCall(
    gas: k::Term<Int>,
    cost: k::Term<Int>,
    account: k::Term<Int>,
) -> k::Term<GasStep>;

k::equations! {
    for ChargeStaticCall;
    use GasResult::*;
    #[k::equation(priority = 40)]
    #[k::requires(gas >= cost)]
    charge_static_call_ecrec    : (gas, cost, 1) => EnoughEcrecPrecompileGas(gas - cost);
    #[k::equation(priority = 40)]
    #[k::requires(gas >= cost)]
    charge_static_call_sha256   : (gas, cost, 2) => EnoughSha256PrecompileGas(gas - cost);
    #[k::equation(priority = 40)]
    #[k::requires(gas >= cost)]
    charge_static_call_ripemd160: (gas, cost, 3) => EnoughRipemd160PrecompileGas(gas - cost);
    #[k::equation(priority = 40)]
    #[k::requires(gas >= cost)]
    charge_static_call_identity : (gas, cost, 4) => EnoughIdentityPrecompileGas(gas - cost);
    #[k::equation(priority = 40)]
    #[k::requires(gas >= cost)]
    charge_static_call_modexp   : (gas, cost, 5) => EnoughModExpPrecompileGas(gas - cost);
    #[k::equation(priority = 40)]
    #[k::requires(gas >= cost)]
    charge_static_call_ecadd    : (gas, cost, 6) => EnoughEcAddPrecompileGas(gas - cost);
    #[k::equation(priority = 40)]
    #[k::requires(gas >= cost)]
    charge_static_call_ecmul    : (gas, cost, 7) => EnoughEcMulPrecompileGas(gas - cost);
    #[k::equation(priority = 40)]
    #[k::requires(gas >= cost)]
    charge_static_call_ecpairing: (gas, cost, 8) => EnoughEcPairingPrecompileGas(gas - cost);
    #[k::equation(priority = 50)]
    #[k::requires(gas >= cost)]
    charge_static_call          : (gas, cost, _) => EnoughGas(Operation::StaticCall, gas - cost);
    #[k::requires(gas < cost)]
    charge_static_call_fails    : (gas, cost, _) => InsufficientGas();
}

#[k::function(total, syntax = "#kevmLookup({program}, {pc})")]
pub fn Lookup(program: k::Term<Bytes>, pc: k::Term<Int>) -> k::Term<OpCode> {
    if pc < 0 {
        Operation::End
    } else if pc < bytes::length(program) {
        Decode {
            opcode: bytes::get(program, pc),
            program,
            pc,
        }
    } else {
        Operation::End
    }
}

#[k::function(total, syntax = "#kevmDecode({opcode}, {program}, {pc})")]
pub fn Decode(opcode: k::Term<Int>, program: k::Term<Bytes>, pc: k::Term<Int>) -> k::Term<OpCode>;

#[k::function(
    total,
    syntax = "#kevmReadImmediate({program}, {at}, {remaining}, {value})"
)]
pub fn ReadImmediate(
    program: k::Term<Bytes>,
    at: k::Term<Int>,
    remaining: k::Term<Int>,
    value: k::Term<Int>,
) -> k::Term<Int> {
    if remaining <= 0 {
        value
    } else {
        ReadImmediate {
            program,
            at: at + 1,
            remaining: remaining - 1,
            value: value * 256 + MemoryByte(program, at),
        }
    }
}

#[k::function(total, syntax = "#kevmValidJumpDestination({program}, {destination})")]
pub fn ValidJumpDestination(program: k::Term<Bytes>, destination: k::Term<Int>) -> k::Term<Bool> {
    if destination >= 0 && destination < bytes::length(program) {
        ScanJumpDestination {
            program,
            destination,
            cursor: 0,
        }
    } else {
        false
    }
}

#[k::function(
    total,
    syntax = "#kevmScanJumpDestination({program}, {destination}, {cursor})"
)]
pub fn ScanJumpDestination(
    program: k::Term<Bytes>,
    destination: k::Term<Int>,
    cursor: k::Term<Int>,
) -> k::Term<Bool> {
    if cursor > destination {
        false
    } else if cursor == destination {
        MemoryByte(program, cursor) == 0x5B
    } else if MemoryByte(program, cursor) >= 0x60 && MemoryByte(program, cursor) <= 0x7F {
        ScanJumpDestination {
            program,
            destination,
            cursor: cursor + (MemoryByte(program, cursor) - 94),
        }
    } else {
        ScanJumpDestination {
            program,
            destination,
            cursor: cursor + 1,
        }
    }
}

#[k::function(total, syntax = "#kevmResolveJump({program}, {destination})")]
pub fn ResolveJump(program: k::Term<Bytes>, destination: k::Term<Int>) -> k::Term<JumpStep> {
    if ValidJumpDestination(program, destination) {
        JumpResult::JumpValid { destination }
    } else {
        JumpResult::JumpInvalid()
    }
}

#[k::function(
    total,
    syntax = "#kevmResolveJumpIf({program}, {destination}, {condition})"
)]
pub fn ResolveJumpIf(
    program: k::Term<Bytes>,
    destination: k::Term<Int>,
    condition: k::Term<Int>,
) -> k::Term<JumpStep> {
    if condition == 0 {
        JumpResult::JumpFallthrough()
    } else {
        ResolveJump {
            program,
            destination,
        }
    }
}

k::equations! {
    for Decode;
    use Operation::*;
    decode_stop               : (0x00, _, _)                  => Stop;
    decode_add                : (0x01, _, _)                  => Add;
    decode_mul                : (0x02, _, _)                  => Mul;
    decode_sub                : (0x03, _, _)                  => Sub;
    decode_div                : (0x04, _, _)                  => Div;
    decode_signed_div         : (0x05, _, _)                  => SignedDiv;
    decode_mod                : (0x06, _, _)                  => Mod;
    decode_signed_mod         : (0x07, _, _)                  => SignedMod;
    decode_add_mod            : (0x08, _, _)                  => AddMod;
    decode_mul_mod            : (0x09, _, _)                  => MulMod;
    decode_exponent           : (0x0A, _, _)                  => Exponent;
    decode_sign_extend        : (0x0B, _, _)                  => SignExtend;
    decode_less_than          : (0x10, _, _)                  => LessThan;
    decode_greater_than       : (0x11, _, _)                  => GreaterThan;
    decode_signed_less_than   : (0x12, _, _)                  => SignedLessThan;
    decode_signed_greater_than: (0x13, _, _)                  => SignedGreaterThan;
    decode_equal              : (0x14, _, _)                  => Equal;
    decode_is_zero            : (0x15, _, _)                  => IsZero;
    decode_bit_and            : (0x16, _, _)                  => BitAnd;
    decode_bit_or             : (0x17, _, _)                  => BitOr;
    decode_bit_xor            : (0x18, _, _)                  => BitXor;
    decode_bit_not            : (0x19, _, _)                  => BitNot;
    decode_byte               : (0x1A, _, _)                  => Byte;
    decode_shift_left         : (0x1B, _, _)                  => ShiftLeft;
    decode_shift_right        : (0x1C, _, _)                  => ShiftRight;
    decode_signed_shift_right : (0x1D, _, _)                  => SignedShiftRight;
    decode_sha3               : (0x20, _, _)                  => Sha3;
    decode_address            : (0x30, _, _)                  => Address;
    decode_balance            : (0x31, _, _)                  => AccountBalance;
    decode_origin             : (0x32, _, _)                  => TxOrigin;
    decode_caller             : (0x33, _, _)                  => MsgCaller;
    decode_call_value         : (0x34, _, _)                  => MsgCallValue;
    decode_call_data_load     : (0x35, _, _)                  => CallDataLoad;
    decode_call_data_size     : (0x36, _, _)                  => CallDataSize;
    decode_call_data_copy     : (0x37, _, _)                  => CallDataCopy;
    decode_code_size          : (0x38, _, _)                  => CodeSize;
    decode_code_copy          : (0x39, _, _)                  => CodeCopy;
    decode_gas_price          : (0x3A, _, _)                  => TxGasPrice;
    decode_external_code_size : (0x3B, _, _)                  => ExternalCodeSize;
    decode_external_code_copy : (0x3C, _, _)                  => ExternalCodeCopy;
    decode_return_data_size   : (0x3D, _, _)                  => ReturnDataSize;
    decode_return_data_copy   : (0x3E, _, _)                  => ReturnDataCopy;
    decode_external_code_hash : (0x3F, _, _)                  => ExternalCodeHash;
    decode_block_hash         : (0x40, _, _)                  => BlockHash;
    decode_coinbase           : (0x41, _, _)                  => BlockCoinbase;
    decode_timestamp          : (0x42, _, _)                  => BlockTimestamp;
    decode_number             : (0x43, _, _)                  => BlockNumber;
    decode_prev_randao        : (0x44, _, _)                  => PrevRandao;
    decode_gas_limit          : (0x45, _, _)                  => BlockGasLimit;
    decode_chain_id           : (0x46, _, _)                  => NetworkChainId;
    decode_self_balance       : (0x47, _, _)                  => SelfBalance;
    decode_base_fee           : (0x48, _, _)                  => BlockBaseFee;
    decode_pop                : (0x50, _, _)                  => Pop;
    decode_memory_load        : (0x51, _, _)                  => MemoryLoad;
    decode_memory_store       : (0x52, _, _)                  => MemoryStore;
    decode_memory_store8      : (0x53, _, _)                  => MemoryStore8;
    decode_storage_load       : (0x54, _, _)                  => StorageLoad;
    decode_storage_store      : (0x55, _, _)                  => StorageStore;
    decode_jump               : (0x56, _, _)                  => Jump;
    decode_jump_if            : (0x57, _, _)                  => JumpIf;
    decode_pc                 : (0x58, _, _)                  => ProgramCounter;
    decode_memory_size        : (0x59, _, _)                  => MemorySize;
    decode_gas_remaining      : (0x5A, _, _)                  => GasRemaining;
    decode_jump_dest          : (0x5B, _, _)                  => JumpDest;
    decode_push_zero          : (0x5F, _, _)                  => PushZero;
    decode_push:
        (k::bits!("011 nnnnn"), program, pc)
        => Push(n + 1, ReadImmediate(program, pc + 1, n + 1, 0));
    decode_duplicate          : (k::bits!("1000 dddd"), _, _) => Duplicate(d + 1);
    decode_swap               : (k::bits!("1001 dddd"), _, _) => Swap(d + 1);
    #[k::requires(t <= 4)]
    decode_log                : (k::bits!("10100 ttt"), _, _) => LogOpcode(t);
    decode_return             : (0xF3, _, _)                  => Return;
    decode_static_call        : (0xFA, _, _)                  => StaticCall;
    decode_revert             : (0xFD, _, _)                  => Revert;
    #[k::equation(owise)]
    decode_invalid            : (_, _, _)                     => Invalid;
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
    #[k::cell(
        name = "account",
        multiplicity = "*",
        cell_type = "Map",
        initial,
        nested
    )]
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
    use Operation::*;
    lookup: {
        k: [ExecutionCommand::Run(), ..],
        program,
        pc,
    } => {
        k: [Lookup { program, pc }, ..],
    };

    begin_push: {
        k: [Push { width, value }, ..],
        word_stack: stack,
        gas,
    } => {
        k: [PreparePush { op: Push { width, value }, stack, gas, cost: 3 }, ..],
    };

    begin_exponent: {
        k: [Exponent(), ..],
        word_stack: [_, w1, ..],
        gas,
    } => {
        k: [ChargeFixed { op: Exponent, gas, cost: ExpCost(w1) }, ..],
    };

    begin_external_code_copy: {
        k: [ExternalCodeCopy(), ..],
        word_stack: [account, destination, _, width, ..],
        memory_used: used,
        accessed_accounts: accessed,
        gas,
    } => {
        k: [
            ChargeFixed {
                op: ExternalCodeCopy,
                gas,
                cost: ExternalCopyGasCost { accessed, account, used, start: destination, width },
            },
            ..,
        ],
    };

    begin_block_hash: {
        k: [BlockHash(), ..],
        word_stack: [_, ..],
        gas,
    } => {
        k: [ChargeFixed { op: BlockHash, gas, cost: 20 }, ..],
    };

    begin_self_balance: {
        k: [SelfBalance(), ..],
        word_stack: stack,
        gas,
    } => {
        k: [PreparePush { op: SelfBalance, stack, gas, cost: 5 }, ..],
    };

    begin_memory_load: {
        k: [MemoryLoad(), ..],
        word_stack: [index, ..],
        memory_used: used,
        gas,
    } => {
        k: [
            ChargeFixed {
                op: MemoryLoad,
                gas,
                cost: 3 + MemoryExpansionCost { used, start: index, width: 32 },
            },
            ..,
        ],
    };

    begin_memory_store: {
        k: [MemoryStore(), ..],
        word_stack: [index, _, ..],
        memory_used: used,
        gas,
    } => {
        k: [
            ChargeFixed {
                op: MemoryStore,
                gas,
                cost: 3 + MemoryExpansionCost { used, start: index, width: 32 },
            },
            ..,
        ],
    };

    begin_memory_store8: {
        k: [MemoryStore8(), ..],
        word_stack: [index, _, ..],
        memory_used: used,
        gas,
    } => {
        k: [
            ChargeFixed {
                op: MemoryStore8,
                gas,
                cost: 3 + MemoryExpansionCost { used, start: index, width: 1 },
            },
            ..,
        ],
    };

    begin_sha3: {
        k: [Sha3(), ..],
        word_stack: [start, width, ..],
        memory_used: used,
        gas,
    } => {
        k: [
            ChargeFixed {
                op: Sha3,
                gas,
                cost: MemoryExpansionCost { used, start, width } + (30 + 6 * ((width + 31) / 32)),
            },
            ..,
        ],
    };

    #[k::requires(current_account == account_id)]
    begin_storage_load: {
        k: [StorageLoad(), ..],
        address: current_account,
        account_id,
        storage,
        accessed_storage: accessed,
        word_stack: [index, ..],
        gas,
    } => {
        k: [
            ChargeFixed {
                op: StorageLoad,
                gas,
                cost: StorageLoadCost {
                    warm: StorageWarm { accessed, account: current_account, index },
                },
            },
            ..,
        ],
    };

    #[k::requires(current_account == account_id)]
    begin_storage_store: {
        k: [StorageStore(), ..],
        address: current_account,
        account_id,
        storage,
        original_storage,
        accessed_storage: accessed,
        static_mode,
        word_stack: [index, new, ..],
        gas,
    } => {
        k: [
            PrepareStorageStore {
                gas,
                original: StorageValue { storage: original_storage, index },
                current: StorageValue { storage, index },
                new,
                warm: StorageWarm { accessed, account: current_account, index },
                static_mode,
            },
            ..,
        ],
    };

    begin_log: {
        k: [LogOpcode { topics }, ..],
        word_stack: stack,
        memory_used: used,
        static_mode,
        gas,
    } => {
        k: [PrepareLog { topics, stack, gas, used, static_mode }, ..],
    };

    begin_jump: {
        k: [Jump(), ..],
        word_stack: [_, ..],
        gas,
    } => {
        k: [ChargeFixed { op: Jump, gas, cost: 8 }, ..],
    };

    begin_jump_if: {
        k: [JumpIf(), ..],
        word_stack: [_, _, ..],
        gas,
    } => {
        k: [ChargeFixed { op: JumpIf, gas, cost: 10 }, ..],
    };

    begin_jump_dest: {
        k: [JumpDest(), ..],
        gas,
    } => {
        k: [ChargeFixed { op: JumpDest, gas, cost: 1 }, ..],
    };

    begin_static_call: {
        k: [StaticCall(), ..],
        word_stack: stack,
        memory_used: used,
        accessed_accounts: accessed,
        gas,
    } => {
        k: [PrepareStaticCall { stack, accessed, used, gas }, ..],
    };

    begin_stop: {
        k: [Stop(), ..],
        gas,
    } => {
        k: [ChargeFixed { op: Stop, gas, cost: 0 }, ..],
    };
}

k::rules! {
    for Machine;
    use Operation::*;

    /// Opcodes that push one word of the call, transaction, or machine state for the base cost of 2 gas.
    begin_push_base_cost_execution: {
        k: [
            op @ (PushZero()
            | Address()
            | TxOrigin()
            | MsgCaller()
            | MsgCallValue()
            | CallDataSize()
            | CodeSize()
            | TxGasPrice()
            | ReturnDataSize()
            | MemorySize()
            | GasRemaining()
            | ProgramCounter()),
            ..,
        ],
        word_stack: stack,
        gas,
    } => {
        k: [PreparePush { op, stack, gas, cost: 2 }, ..],
    };

    /// Opcodes that push one word of the block header for the base cost of 2 gas.
    begin_push_base_cost_block: {
        k: [
            op @ (BlockCoinbase()
            | BlockTimestamp()
            | BlockNumber()
            | PrevRandao()
            | BlockGasLimit()
            | NetworkChainId()
            | BlockBaseFee()),
            ..,
        ],
        word_stack: stack,
        gas,
    } => {
        k: [PreparePush { op, stack, gas, cost: 2 }, ..],
    };

    /// POP, DUP, and SWAP, whose stack bounds `PrepareStack` checks before charging.
    begin_stack_operation: {
        k: [op @ (Pop() | Duplicate { .. } | Swap { .. }), ..],
        word_stack: stack,
        gas,
    } => {
        k: [PrepareStack { op, stack, gas }, ..],
    };

    /// Two-operand opcodes that cost 3 gas.
    begin_binary_very_low: {
        k: [
            op @ (Add()
            | Sub()
            | LessThan()
            | GreaterThan()
            | SignedLessThan()
            | SignedGreaterThan()
            | Equal()
            | BitAnd()
            | BitOr()
            | BitXor()
            | Byte()
            | ShiftLeft()
            | ShiftRight()
            | SignedShiftRight()),
            ..,
        ],
        word_stack: [_, _, ..],
        gas,
    } => {
        k: [ChargeFixed { op, gas, cost: 3 }, ..],
    };

    /// Two-operand opcodes that cost 5 gas.
    begin_binary_low: {
        k: [op @ (Mul() | Div() | SignedDiv() | Mod() | SignedMod() | SignExtend()), ..],
        word_stack: [_, _, ..],
        gas,
    } => {
        k: [ChargeFixed { op, gas, cost: 5 }, ..],
    };

    /// Three-operand modular opcodes that cost 8 gas.
    begin_ternary_mid: {
        k: [op @ (AddMod() | MulMod()), ..],
        word_stack: [_, _, _, ..],
        gas,
    } => {
        k: [ChargeFixed { op, gas, cost: 8 }, ..],
    };

    /// One-operand opcodes that cost 3 gas.
    begin_unary_very_low: {
        k: [op @ (IsZero() | BitNot() | CallDataLoad()), ..],
        word_stack: [_, ..],
        gas,
    } => {
        k: [ChargeFixed { op, gas, cost: 3 }, ..],
    };

    /// One-operand account queries charged the warm or cold account-access cost.
    begin_account_access: {
        k: [op @ (AccountBalance() | ExternalCodeSize() | ExternalCodeHash()), ..],
        word_stack: [account, ..],
        accessed_accounts: accessed,
        gas,
    } => {
        k: [ChargeFixed { op, gas, cost: AccountAccessCost(accessed, account) }, ..],
    };

    /// Copies from call data, code, or return data into memory, charged by width and memory expansion.
    begin_copy: {
        k: [op @ (CallDataCopy() | CodeCopy() | ReturnDataCopy()), ..],
        word_stack: [destination, _, width, ..],
        memory_used: used,
        gas,
    } => {
        k: [ChargeFixed { op, gas, cost: CopyGasCost(used, destination, width) }, ..],
    };

    /// RETURN and REVERT, charged the memory expansion of their output range.
    begin_return_or_revert: {
        k: [op @ (Return() | Revert()), ..],
        word_stack: [start, width, ..],
        memory_used: used,
        gas,
    } => {
        k: [ChargeFixed { op, gas, cost: MemoryExpansionCost(used, start, width) }, ..],
    };
}

k::rules! {
    for Machine;
    use ExecutionCommand::*;
    use GasResult::*;
    use Operation::*;
    use PrecompileResult::*;
    use JumpResult::*;
    use CopyResult::*;
    exec_push: {
        k: [EnoughGas(Push { width, value }, remaining), ..],
        word_stack: stack,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [Chop(value), ..stack],
        pc: pc + (width + 1),
        gas: remaining,
    };

    exec_push_zero: {
        k: [EnoughGas(PushZero(), remaining), ..],
        word_stack: stack,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [0, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_pop: {
        k: [EnoughGas(Pop(), remaining), ..],
        word_stack: [_, tail @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: tail,
        pc: pc + 1,
        gas: remaining,
    };

    exec_duplicate: {
        k: [EnoughGas(Duplicate { depth }, remaining), ..],
        word_stack: stack,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [StackAt { stack, index: depth - 1 }, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_swap: {
        k: [EnoughGas(Swap { depth }, remaining), ..],
        word_stack: [head, tail @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [
            StackAt { stack: tail, index: depth - 1 },
            ..StackSet { stack: tail, index: depth - 1, value: head },
        ],
        pc: pc + 1,
        gas: remaining,
    };

    exec_add: {
        k: [EnoughGas(Add(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [Chop(w0 + w1), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_mul: {
        k: [EnoughGas(Mul(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [Chop(w0 * w1), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_sub: {
        k: [EnoughGas(Sub(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [Chop(w0 - w1), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_div: {
        k: [EnoughGas(Div(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [WordDiv { dividend: w0, divisor: w1 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_signed_div: {
        k: [EnoughGas(SignedDiv(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [SignedWordDiv { dividend: w0, divisor: w1 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_mod: {
        k: [EnoughGas(Mod(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [WordMod { dividend: w0, divisor: w1 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_signed_mod: {
        k: [EnoughGas(SignedMod(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [SignedWordMod { dividend: w0, divisor: w1 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_add_mod: {
        k: [EnoughGas(AddMod(), remaining), ..],
        word_stack: [w0, w1, w2, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [WordMod { dividend: w0 + w1, divisor: w2 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_mul_mod: {
        k: [EnoughGas(MulMod(), remaining), ..],
        word_stack: [w0, w1, w2, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [WordMod { dividend: w0 * w1, divisor: w2 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_exponent: {
        k: [EnoughGas(Exponent(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [int::pow_mod(w0, w1, POW256), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_sign_extend: {
        k: [EnoughGas(SignExtend(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [WordSignExtend { index: w0, value: w1 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_less_than: {
        k: [EnoughGas(LessThan(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [BoolToWord(w0 < w1), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_greater_than: {
        k: [EnoughGas(GreaterThan(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [BoolToWord(w0 > w1), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_signed_less_than: {
        k: [EnoughGas(SignedLessThan(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [SignedLess { left: w0, right: w1 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_signed_greater_than: {
        k: [EnoughGas(SignedGreaterThan(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [SignedLess { left: w1, right: w0 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_equal: {
        k: [EnoughGas(Equal(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [BoolToWord(w0 == w1), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_is_zero: {
        k: [EnoughGas(IsZero(), remaining), ..],
        word_stack: [w0, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [BoolToWord(w0 == 0), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_bit_and: {
        k: [EnoughGas(BitAnd(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [w0 & w1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_bit_or: {
        k: [EnoughGas(BitOr(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [w0 | w1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_bit_xor: {
        k: [EnoughGas(BitXor(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [w0 ^ w1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_bit_not: {
        k: [EnoughGas(BitNot(), remaining), ..],
        word_stack: [w0, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [w0 ^ (POW256 - 1), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_byte: {
        k: [EnoughGas(Byte(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [WordByte { index: w0, value: w1 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_shift_left: {
        k: [EnoughGas(ShiftLeft(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [WordShiftLeft { value: w1, shift: w0 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_shift_right: {
        k: [EnoughGas(ShiftRight(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [WordShiftRight { value: w1, shift: w0 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_signed_shift_right: {
        k: [EnoughGas(SignedShiftRight(), remaining), ..],
        word_stack: [w0, w1, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [WordSignedShiftRight { value: w1, shift: w0 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_address: {
        k: [EnoughGas(Address(), remaining), ..],
        word_stack: stack,
        address: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::requires(account == present_account)]
    #[k::rule(label = "balance-true")]
    exec_balance_present: {
        k: [EnoughGas(AccountBalance(), remaining), ..],
        account_id: present_account,
        balance,
        accessed_accounts: accessed,
        word_stack: [account, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        accessed_accounts: MarkAccountAccess { accessed, account },
        word_stack: [balance, ..],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::rule(owise, label = "balance-false")]
    exec_balance_absent: {
        k: [EnoughGas(AccountBalance(), remaining), ..],
        accessed_accounts: accessed,
        word_stack: [account, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        accessed_accounts: MarkAccountAccess { accessed, account },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_origin: {
        k: [EnoughGas(TxOrigin(), remaining), ..],
        word_stack: stack,
        origin: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_caller: {
        k: [EnoughGas(MsgCaller(), remaining), ..],
        word_stack: stack,
        caller: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_call_value: {
        k: [EnoughGas(MsgCallValue(), remaining), ..],
        word_stack: stack,
        call_value: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_call_data_load: {
        k: [EnoughGas(CallDataLoad(), remaining), ..],
        call_data,
        word_stack: [index, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [ReadMemoryWord { memory: call_data, index, remaining: 32, value: 0 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_call_data_size: {
        k: [EnoughGas(CallDataSize(), remaining), ..],
        word_stack: stack,
        call_data: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [bytes::length(value), ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_call_data_copy: {
        k: [EnoughGas(CallDataCopy(), remaining), ..],
        call_data,
        local_mem: memory,
        memory_used: used,
        word_stack: [destination, source_index, width, rest @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        local_mem: CopyBytes {
            memory: PrepareCopyMemory { memory, used, start: destination, width },
            destination,
            source: call_data,
            source_index,
            remaining: width,
        },
        memory_used: MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: pc + 1,
        gas: remaining,
    };

    exec_code_size: {
        k: [EnoughGas(CodeSize(), remaining), ..],
        program: value,
        word_stack: stack,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [bytes::length(value), ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_code_copy: {
        k: [EnoughGas(CodeCopy(), remaining), ..],
        program,
        local_mem: memory,
        memory_used: used,
        word_stack: [destination, source_index, width, rest @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        local_mem: CopyBytes {
            memory: PrepareCopyMemory { memory, used, start: destination, width },
            destination,
            source: program,
            source_index,
            remaining: width,
        },
        memory_used: MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: pc + 1,
        gas: remaining,
    };

    exec_gas_price: {
        k: [EnoughGas(TxGasPrice(), remaining), ..],
        word_stack: stack,
        gas_price: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::requires(account == present_account)]
    #[k::rule(label = "extcodesize-true")]
    exec_external_code_size_present: {
        k: [EnoughGas(ExternalCodeSize(), remaining), ..],
        account_id: present_account,
        code,
        accessed_accounts: accessed,
        word_stack: [account, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        accessed_accounts: MarkAccountAccess { accessed, account },
        word_stack: [bytes::length(code), ..],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::rule(owise, label = "extcodesize-false")]
    exec_external_code_size_absent: {
        k: [EnoughGas(ExternalCodeSize(), remaining), ..],
        accessed_accounts: accessed,
        word_stack: [account, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        accessed_accounts: MarkAccountAccess { accessed, account },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::requires(account == present_account)]
    #[k::rule(label = "extcodecopy-true")]
    exec_external_code_copy_present: {
        k: [EnoughGas(ExternalCodeCopy(), remaining), ..],
        account_id: present_account,
        code,
        accessed_accounts: accessed,
        local_mem: memory,
        memory_used: used,
        word_stack: [account, destination, source_index, width, rest @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        accessed_accounts: MarkAccountAccess { accessed, account },
        local_mem: CopyBytes {
            memory: PrepareCopyMemory { memory, used, start: destination, width },
            destination,
            source: code,
            source_index,
            remaining: width,
        },
        memory_used: MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: pc + 1,
        gas: remaining,
    };

    #[k::rule(owise, label = "extcodecopy-false")]
    exec_external_code_copy_absent: {
        k: [EnoughGas(ExternalCodeCopy(), remaining), ..],
        accessed_accounts: accessed,
        local_mem: memory,
        memory_used: used,
        word_stack: [account, destination, source_index, width, rest @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        accessed_accounts: MarkAccountAccess { accessed, account },
        local_mem: CopyBytes {
            memory: PrepareCopyMemory { memory, used, start: destination, width },
            destination,
            source: bytes::empty(),
            source_index,
            remaining: width,
        },
        memory_used: MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: pc + 1,
        gas: remaining,
    };

    #[k::requires(
        account == present_account && !AccountEmpty { code, nonce, balance }
    )]
    #[k::rule(label = "extcodehash-true")]
    exec_external_code_hash_nonempty: {
        k: [EnoughGas(ExternalCodeHash(), remaining), ..],
        account_id: present_account,
        balance,
        code,
        nonce,
        accessed_accounts: accessed,
        word_stack: [account, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        accessed_accounts: MarkAccountAccess { accessed, account },
        word_stack: [Keccak(code), ..],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::rule(owise, label = "extcodehash-false")]
    exec_external_code_hash_empty_or_absent: {
        k: [EnoughGas(ExternalCodeHash(), remaining), ..],
        accessed_accounts: accessed,
        word_stack: [account, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        accessed_accounts: MarkAccountAccess { accessed, account },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_return_data_size: {
        k: [EnoughGas(ReturnDataSize(), remaining), ..],
        word_stack: stack,
        output: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [bytes::length(value), ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    inspect_return_data_copy: {
        k: [EnoughGas(ReturnDataCopy(), remaining), ..],
        output,
        word_stack: [_, source_index, width, ..],
    } => {
        k: [ResolveReturnDataCopy { output, source_index, width, remaining }, ..],
    };

    exec_return_data_copy_valid: {
        k: [ReturnDataCopyValid { remaining }, ..],
        output,
        local_mem: memory,
        memory_used: used,
        word_stack: [destination, source_index, width, rest @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        local_mem: CopyBytes {
            memory: PrepareCopyMemory { memory, used, start: destination, width },
            destination,
            source: output,
            source_index,
            remaining: width,
        },
        memory_used: MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        pc: pc + 1,
        gas: remaining,
    };

    exec_return_data_copy_invalid: {
        k: [ReturnDataCopyInvalid { remaining }, ..],
        memory_used: used,
        word_stack: [destination, _, width, rest @ ..],
        gas: _,
        status_code: _,
    } => {
        k: [..],
        memory_used: MemoryUsageUpdate { used, start: destination, width },
        word_stack: rest,
        gas: remaining,
        status_code: Status::InvalidMemoryAccess(),
    };

    exec_block_hash: {
        k: [EnoughGas(BlockHash(), remaining), ..],
        block_hashes: hashes,
        number,
        word_stack: [requested, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [BlockHashLookup { hashes, requested, highest: number - 1, age: 0 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_coinbase: {
        k: [EnoughGas(BlockCoinbase(), remaining), ..],
        word_stack: stack,
        coinbase: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_timestamp: {
        k: [EnoughGas(BlockTimestamp(), remaining), ..],
        word_stack: stack,
        timestamp: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_number: {
        k: [EnoughGas(BlockNumber(), remaining), ..],
        word_stack: stack,
        number: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_prev_randao: {
        k: [EnoughGas(PrevRandao(), remaining), ..],
        word_stack: stack,
        prev_randao: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_gas_limit: {
        k: [EnoughGas(BlockGasLimit(), remaining), ..],
        word_stack: stack,
        gas_limit: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_chain_id: {
        k: [EnoughGas(NetworkChainId(), remaining), ..],
        word_stack: stack,
        chain_id: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::requires(account == present_account)]
    exec_self_balance: {
        k: [EnoughGas(SelfBalance(), remaining), ..],
        address: account,
        account_id: present_account,
        balance,
        word_stack: stack,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [balance, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_base_fee: {
        k: [EnoughGas(BlockBaseFee(), remaining), ..],
        word_stack: stack,
        base_fee: value,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [value, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_memory_load: {
        k: [EnoughGas(MemoryLoad(), remaining), ..],
        local_mem: memory,
        memory_used: used,
        word_stack: [index, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        memory_used: MemoryUsageUpdate { used, start: index, width: 32 },
        word_stack: [ReadMemoryWord { memory, index, remaining: 32, value: 0 }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_memory_store: {
        k: [EnoughGas(MemoryStore(), remaining), ..],
        local_mem: memory,
        memory_used: used,
        word_stack: [index, value, rest @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        local_mem: WriteMemoryWord {
            memory: bytes::pad_right(
                memory,
                MemoryUsageUpdate { used, start: index, width: 32 } * 32,
                0,
            ),
            index,
            remaining: 32,
            value: Chop(value),
        },
        memory_used: MemoryUsageUpdate { used, start: index, width: 32 },
        word_stack: rest,
        pc: pc + 1,
        gas: remaining,
    };

    exec_memory_store8: {
        k: [EnoughGas(MemoryStore8(), remaining), ..],
        local_mem: memory,
        memory_used: used,
        word_stack: [index, value, rest @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        local_mem: bytes::update(
            bytes::pad_right(memory, MemoryUsageUpdate { used, start: index, width: 1 } * 32, 0),
            index,
            int::rem_euclid(value, 256),
        ),
        memory_used: MemoryUsageUpdate { used, start: index, width: 1 },
        word_stack: rest,
        pc: pc + 1,
        gas: remaining,
    };

    exec_sha3: {
        k: [EnoughGas(Sha3(), remaining), ..],
        local_mem: memory,
        memory_used: used,
        word_stack: [start, width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        memory_used: MemoryUsageUpdate { used, start, width },
        word_stack: [Keccak(ReturnBytes(memory, start, width)), ..],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::requires(current_account == account_id)]
    exec_storage_load: {
        k: [EnoughGas(StorageLoad(), remaining), ..],
        address: current_account,
        account_id,
        storage,
        accessed_storage: accessed,
        word_stack: [index, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        accessed_storage: MarkStorageAccess { accessed, account: current_account, index },
        word_stack: [StorageValue { storage, index }, ..],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::requires(current_account == account_id)]
    exec_storage_store: {
        k: [EnoughGas(StorageStore(), remaining), ..],
        address: current_account,
        account_id,
        storage,
        original_storage,
        accessed_storage: accessed,
        refund,
        word_stack: [index, new, rest @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        storage: map::update(storage, index, new),
        accessed_storage: MarkStorageAccess { accessed, account: current_account, index },
        refund: refund + StorageRefundDelta {
            original: StorageValue { storage: original_storage, index },
            current: StorageValue { storage, index },
            new,
        },
        word_stack: rest,
        pc: pc + 1,
        gas: remaining,
    };

    exec_log: {
        k: [EnoughGas(LogOpcode { topics }, remaining), ..],
        address,
        logs,
        local_mem: memory,
        memory_used: used,
        word_stack: [start, width, topic_stack @ ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        logs: [
            ..logs,
            LogRecord::Entry {
                address,
                topics: StackTakeList { stack: topic_stack, remaining: topics },
                data: ReturnBytes(memory, start, width),
            },
        ],
        memory_used: MemoryUsageUpdate { used, start, width },
        word_stack: StackDrop { stack: topic_stack, remaining: topics },
        pc: pc + 1,
        gas: remaining,
    };

    exec_memory_size: {
        k: [EnoughGas(MemorySize(), remaining), ..],
        memory_used: used,
        word_stack: stack,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [Chop(32 * used), ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_gas_remaining: {
        k: [EnoughGas(GasRemaining(), remaining), ..],
        word_stack: stack,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [remaining, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    exec_pc: {
        k: [EnoughGas(ProgramCounter(), remaining), ..],
        word_stack: stack,
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        word_stack: [pc, ..stack],
        pc: pc + 1,
        gas: remaining,
    };

    inspect_jump_destination: {
        k: [EnoughGas(Jump(), remaining), ..],
        program,
        word_stack: [destination, rest @ ..],
        gas: _,
    } => {
        k: [ResolveJump { program, destination }, ..],
        word_stack: rest,
        gas: remaining,
    };

    inspect_jump_if_destination: {
        k: [EnoughGas(JumpIf(), remaining), ..],
        program,
        word_stack: [destination, condition, rest @ ..],
        gas: _,
    } => {
        k: [ResolveJumpIf { program, destination, condition }, ..],
        word_stack: rest,
        gas: remaining,
    };

    exec_valid_jump: {
        k: [JumpValid { destination }, ..],
        pc: _,
    } => {
        k: [Run(), ..],
        pc: destination,
    };

    exec_false_jump_if: {
        k: [JumpFallthrough(), ..],
        pc,
    } => {
        k: [Run(), ..],
        pc: pc + 1,
    };

    exec_invalid_jump: {
        k: [JumpInvalid(), ..],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::BadJumpDestination(),
    };

    exec_jump_dest: {
        k: [EnoughGas(JumpDest(), remaining), ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_return: {
        k: [EnoughGas(Return(), remaining), ..],
        output: _,
        local_mem: memory,
        memory_used: used,
        word_stack: [start, width, rest @ ..],
        gas: _,
        status_code: _,
    } => {
        k: [..],
        output: ReturnBytes(memory, start, width),
        memory_used: MemoryUsageUpdate { used, start, width },
        word_stack: rest,
        gas: remaining,
        status_code: Status::Success(),
    };

    exec_revert: {
        k: [EnoughGas(Revert(), remaining), ..],
        output: _,
        local_mem: memory,
        memory_used: used,
        word_stack: [start, width, rest @ ..],
        gas: _,
        status_code: _,
    } => {
        k: [..],
        output: ReturnBytes(memory, start, width),
        memory_used: MemoryUsageUpdate { used, start, width },
        word_stack: rest,
        gas: remaining,
        status_code: Status::Reverted(),
    };

    begin_static_call_ecrec: {
        k: [EnoughEcrecPrecompileGas { remaining }, ..],
        word_stack: [
            gas_cap,
            1,
            argument_start,
            argument_width,
            return_start,
            return_width,
            rest @ ..,
        ],
    } => {
        k: [ResolveEcrecPrecompile { requested: gas_cap, available: remaining }, ..],
    };

    exec_static_call_ecrec_success: {
        k: [EcrecPrecompileSuccess { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 1, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(1),
        ),
        output: EcrecPrecompileOutput { data: ReturnBytes(memory, argument_start, argument_width) },
        local_mem: CopyBytes {
            memory: PrepareCopyMemory {
                memory: PrepareCopyMemory {
                    memory,
                    used,
                    start: argument_start,
                    width: argument_width,
                },
                used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
                start: return_start,
                width: return_width,
            },
            destination: return_start,
            source: EcrecPrecompileOutput {
                data: ReturnBytes(memory, argument_start, argument_width),
            },
            source_index: 0,
            remaining: Minimum(
                return_width,
                bytes::length(EcrecPrecompileOutput {
                    data: ReturnBytes(memory, argument_start, argument_width),
                }),
            ),
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 1 },
        word_stack: [1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_static_call_ecrec_exception: {
        k: [EcrecPrecompileFailure { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 1, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(1),
        ),
        output: bytes::empty(),
        local_mem: PrepareCopyMemory {
            memory: PrepareCopyMemory {
                memory,
                used,
                start: argument_start,
                width: argument_width,
            },
            used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
            start: return_start,
            width: return_width,
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 1 },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    begin_static_call_sha256: {
        k: [EnoughSha256PrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: [
            gas_cap,
            2,
            argument_start,
            argument_width,
            return_start,
            return_width,
            rest @ ..,
        ],
    } => {
        k: [
            ResolveSha256Precompile {
                data: ReturnBytes(memory, argument_start, argument_width),
                requested: gas_cap,
                available: remaining,
            },
            ..,
        ],
    };

    exec_static_call_sha256_success: {
        k: [Sha256PrecompileSuccess { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 2, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(2),
        ),
        output: Sha256Digest { value: ReturnBytes(memory, argument_start, argument_width) },
        local_mem: CopyBytes {
            memory: PrepareCopyMemory {
                memory: PrepareCopyMemory {
                    memory,
                    used,
                    start: argument_start,
                    width: argument_width,
                },
                used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
                start: return_start,
                width: return_width,
            },
            destination: return_start,
            source: Sha256Digest { value: ReturnBytes(memory, argument_start, argument_width) },
            source_index: 0,
            remaining: Minimum(return_width, 32),
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 2 },
        word_stack: [1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_static_call_sha256_exception: {
        k: [Sha256PrecompileFailure { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 2, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(2),
        ),
        output: bytes::empty(),
        local_mem: PrepareCopyMemory {
            memory: PrepareCopyMemory {
                memory,
                used,
                start: argument_start,
                width: argument_width,
            },
            used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
            start: return_start,
            width: return_width,
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 2 },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    begin_static_call_ripemd160: {
        k: [EnoughRipemd160PrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: [
            gas_cap,
            3,
            argument_start,
            argument_width,
            return_start,
            return_width,
            rest @ ..,
        ],
    } => {
        k: [
            ResolveRipemd160Precompile {
                data: ReturnBytes(memory, argument_start, argument_width),
                requested: gas_cap,
                available: remaining,
            },
            ..,
        ],
    };

    exec_static_call_ripemd160_success: {
        k: [Ripemd160PrecompileSuccess { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 3, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(3),
        ),
        output: CopyBytes {
            memory: bytes::pad_right(bytes::empty(), 32, 0),
            destination: 12,
            source: Ripemd160Digest { value: ReturnBytes(memory, argument_start, argument_width) },
            source_index: 0,
            remaining: 20,
        },
        local_mem: CopyBytes {
            memory: PrepareCopyMemory {
                memory: PrepareCopyMemory {
                    memory,
                    used,
                    start: argument_start,
                    width: argument_width,
                },
                used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
                start: return_start,
                width: return_width,
            },
            destination: return_start,
            source: CopyBytes {
                memory: bytes::pad_right(bytes::empty(), 32, 0),
                destination: 12,
                source: Ripemd160Digest {
                    value: ReturnBytes(memory, argument_start, argument_width),
                },
                source_index: 0,
                remaining: 20,
            },
            source_index: 0,
            remaining: Minimum(return_width, 32),
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 3 },
        word_stack: [1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_static_call_ripemd160_exception: {
        k: [Ripemd160PrecompileFailure { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 3, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(3),
        ),
        output: bytes::empty(),
        local_mem: PrepareCopyMemory {
            memory: PrepareCopyMemory {
                memory,
                used,
                start: argument_start,
                width: argument_width,
            },
            used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
            start: return_start,
            width: return_width,
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 3 },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    begin_static_call_identity: {
        k: [EnoughIdentityPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: [
            gas_cap,
            4,
            argument_start,
            argument_width,
            return_start,
            return_width,
            rest @ ..,
        ],
    } => {
        k: [
            ResolveIdentityPrecompile {
                data: ReturnBytes(memory, argument_start, argument_width),
                requested: gas_cap,
                available: remaining,
            },
            ..,
        ],
    };

    exec_static_call_identity_success: {
        k: [IdentityPrecompileSuccess { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 4, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(4),
        ),
        output: ReturnBytes(memory, argument_start, argument_width),
        local_mem: CopyBytes {
            memory: PrepareCopyMemory {
                memory: PrepareCopyMemory {
                    memory,
                    used,
                    start: argument_start,
                    width: argument_width,
                },
                used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
                start: return_start,
                width: return_width,
            },
            destination: return_start,
            source: ReturnBytes(memory, argument_start, argument_width),
            source_index: 0,
            remaining: Minimum(return_width, argument_width),
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 4 },
        word_stack: [1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_static_call_identity_exception: {
        k: [IdentityPrecompileFailure { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 4, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(4),
        ),
        output: bytes::empty(),
        local_mem: PrepareCopyMemory {
            memory: PrepareCopyMemory {
                memory,
                used,
                start: argument_start,
                width: argument_width,
            },
            used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
            start: return_start,
            width: return_width,
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 4 },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    begin_static_call_modexp: {
        k: [EnoughModExpPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: [
            gas_cap,
            5,
            argument_start,
            argument_width,
            return_start,
            return_width,
            rest @ ..,
        ],
    } => {
        k: [
            ResolveModExpPrecompile {
                data: ReturnBytes(memory, argument_start, argument_width),
                requested: gas_cap,
                available: remaining,
            },
            ..,
        ],
    };

    exec_static_call_modexp_success: {
        k: [ModExpPrecompileSuccess { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 5, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(5),
        ),
        output: ModExpPrecompileOutput {
            data: ReturnBytes(memory, argument_start, argument_width),
        },
        local_mem: CopyBytes {
            memory: PrepareCopyMemory {
                memory: PrepareCopyMemory {
                    memory,
                    used,
                    start: argument_start,
                    width: argument_width,
                },
                used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
                start: return_start,
                width: return_width,
            },
            destination: return_start,
            source: ModExpPrecompileOutput {
                data: ReturnBytes(memory, argument_start, argument_width),
            },
            source_index: 0,
            remaining: Minimum(
                return_width,
                bytes::length(ModExpPrecompileOutput {
                    data: ReturnBytes(memory, argument_start, argument_width),
                }),
            ),
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 5 },
        word_stack: [1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_static_call_modexp_exception: {
        k: [ModExpPrecompileFailure { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 5, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(5),
        ),
        output: bytes::empty(),
        local_mem: PrepareCopyMemory {
            memory: PrepareCopyMemory {
                memory,
                used,
                start: argument_start,
                width: argument_width,
            },
            used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
            start: return_start,
            width: return_width,
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 5 },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    begin_static_call_ecadd: {
        k: [EnoughEcAddPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: [
            gas_cap,
            6,
            argument_start,
            argument_width,
            return_start,
            return_width,
            rest @ ..,
        ],
    } => {
        k: [
            ResolveEcAddPrecompile {
                data: ReturnBytes(memory, argument_start, argument_width),
                requested: gas_cap,
                available: remaining,
            },
            ..,
        ],
    };

    exec_static_call_ecadd_success: {
        k: [EcAddPrecompileSuccess { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 6, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(6),
        ),
        output: EcAddPrecompileOutput { data: ReturnBytes(memory, argument_start, argument_width) },
        local_mem: CopyBytes {
            memory: PrepareCopyMemory {
                memory: PrepareCopyMemory {
                    memory,
                    used,
                    start: argument_start,
                    width: argument_width,
                },
                used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
                start: return_start,
                width: return_width,
            },
            destination: return_start,
            source: EcAddPrecompileOutput {
                data: ReturnBytes(memory, argument_start, argument_width),
            },
            source_index: 0,
            remaining: Minimum(return_width, 64),
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 6 },
        word_stack: [1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_static_call_ecadd_exception: {
        k: [EcAddPrecompileFailure { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 6, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(6),
        ),
        output: bytes::empty(),
        local_mem: PrepareCopyMemory {
            memory: PrepareCopyMemory {
                memory,
                used,
                start: argument_start,
                width: argument_width,
            },
            used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
            start: return_start,
            width: return_width,
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 6 },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    begin_static_call_ecmul: {
        k: [EnoughEcMulPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: [
            gas_cap,
            7,
            argument_start,
            argument_width,
            return_start,
            return_width,
            rest @ ..,
        ],
    } => {
        k: [
            ResolveEcMulPrecompile {
                data: ReturnBytes(memory, argument_start, argument_width),
                requested: gas_cap,
                available: remaining,
            },
            ..,
        ],
    };

    exec_static_call_ecmul_success: {
        k: [EcMulPrecompileSuccess { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 7, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(7),
        ),
        output: EcMulPrecompileOutput { data: ReturnBytes(memory, argument_start, argument_width) },
        local_mem: CopyBytes {
            memory: PrepareCopyMemory {
                memory: PrepareCopyMemory {
                    memory,
                    used,
                    start: argument_start,
                    width: argument_width,
                },
                used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
                start: return_start,
                width: return_width,
            },
            destination: return_start,
            source: EcMulPrecompileOutput {
                data: ReturnBytes(memory, argument_start, argument_width),
            },
            source_index: 0,
            remaining: Minimum(return_width, 64),
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 7 },
        word_stack: [1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_static_call_ecmul_exception: {
        k: [EcMulPrecompileFailure { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 7, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(7),
        ),
        output: bytes::empty(),
        local_mem: PrepareCopyMemory {
            memory: PrepareCopyMemory {
                memory,
                used,
                start: argument_start,
                width: argument_width,
            },
            used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
            start: return_start,
            width: return_width,
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 7 },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    begin_static_call_ecpairing: {
        k: [EnoughEcPairingPrecompileGas { remaining }, ..],
        local_mem: memory,
        word_stack: [
            gas_cap,
            8,
            argument_start,
            argument_width,
            return_start,
            return_width,
            rest @ ..,
        ],
    } => {
        k: [
            ResolveEcPairingPrecompile {
                data: ReturnBytes(memory, argument_start, argument_width),
                requested: gas_cap,
                available: remaining,
            },
            ..,
        ],
    };

    exec_static_call_ecpairing_success: {
        k: [EcPairingPrecompileSuccess { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 8, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(8),
        ),
        output: EcPairingPrecompileOutput {
            data: ReturnBytes(memory, argument_start, argument_width),
        },
        local_mem: CopyBytes {
            memory: PrepareCopyMemory {
                memory: PrepareCopyMemory {
                    memory,
                    used,
                    start: argument_start,
                    width: argument_width,
                },
                used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
                start: return_start,
                width: return_width,
            },
            destination: return_start,
            source: EcPairingPrecompileOutput {
                data: ReturnBytes(memory, argument_start, argument_width),
            },
            source_index: 0,
            remaining: Minimum(return_width, 32),
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 8 },
        word_stack: [1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_static_call_ecpairing_exception: {
        k: [EcPairingPrecompileFailure { remaining }, ..],
        touched_accounts,
        output: _,
        address,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [_, 8, argument_start, argument_width, return_start, return_width, ..],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(8),
        ),
        output: bytes::empty(),
        local_mem: PrepareCopyMemory {
            memory: PrepareCopyMemory {
                memory,
                used,
                start: argument_start,
                width: argument_width,
            },
            used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
            start: return_start,
            width: return_width,
        },
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account: 8 },
        word_stack: [0, ..],
        pc: pc + 1,
        gas: remaining,
    };

    #[k::requires(
        account > 9
            && account == present_account
            && !AccountEmpty { code, nonce, balance }
    )]
    exec_static_call_nonempty: {
        k: [EnoughGas(StaticCall(), remaining), ..],
        call_stack,
        interim_states,
        touched_accounts,
        account_id: present_account,
        balance,
        code,
        nonce,
        storage,
        original_storage,
        output: _,
        status_code: _,
        self_destruct,
        logs,
        refund,
        accessed_accounts: accessed,
        accessed_storage,
        created_accounts,
        call_state: caller_frame @ CallState {
            address,
            local_mem: memory,
            memory_used: used,
            word_stack: [
                gas_cap,
                account,
                argument_start,
                argument_width,
                return_start,
                return_width,
                rest @ ..,
            ],
            pc,
            call_depth,
            ..
        },
    } => {
        k: [Run(), FinishStaticCall { return_start, return_width }, ..],
        call_stack: [
            CallState {
                word_stack: rest,
                local_mem: PrepareCopyMemory {
                    memory: PrepareCopyMemory {
                        memory,
                        used,
                        start: argument_start,
                        width: argument_width,
                    },
                    used: MemoryUsageUpdate { used, start: argument_start, width: argument_width },
                    start: return_start,
                    width: return_width,
                },
                pc: pc + 1,
                gas: remaining - StaticCallGas { requested: gas_cap, available: remaining },
                memory_used: CallMemoryUsage {
                    used,
                    argument_start,
                    argument_width,
                    return_start,
                    return_width,
                },
                call_gas: StaticCallGas { requested: gas_cap, available: remaining },
                ..caller_frame
            },
            ..call_stack,
        ],
        interim_states: [
            SavedWorldState::Snapshot {
                account_id: present_account,
                balance,
                code,
                nonce,
                storage,
                original_storage,
                self_destruct,
                logs,
                refund,
                accessed_accounts: MarkAccountAccess { accessed, account },
                accessed_storage,
                created_accounts,
            },
            ..interim_states,
        ],
        touched_accounts: set::union(
            set::union(touched_accounts, set::item(address)),
            set::item(account),
        ),
        output: bytes::empty(),
        status_code: Status::Running(),
        accessed_accounts: MarkAccountAccess { accessed, account },
        call_state: CallState {
            program: code,
            jump_dests: bytes::empty(),
            address: account,
            caller: address,
            call_data: ReturnBytes(memory, argument_start, argument_width),
            call_value: 0,
            word_stack: [],
            local_mem: bytes::empty(),
            pc: 0,
            gas: StaticCallGas { requested: gas_cap, available: remaining },
            memory_used: 0,
            call_gas: 0,
            static_mode: true,
            call_depth: call_depth + 1,
            code_address: account,
        },
    };

    finish_static_call_success: {
        k: [FinishStaticCall { return_start, return_width }, ..],
        call_stack: [
            caller_frame @ CallState {
                word_stack: caller_stack,
                local_mem: caller_memory,
                gas: caller_gas,
                ..
            },
            remaining_call_stack @ ..,
        ],
        interim_states: [saved_world_state, remaining_interim_states @ ..],
        output: child_output,
        status_code: Status::Success(),
        call_state: CallState { gas: child_gas, .. },
    } => {
        k: [Run(), ..],
        call_stack: remaining_call_stack,
        interim_states: remaining_interim_states,
        status_code: Status::Running(),
        call_state: CallState {
            word_stack: [1, ..caller_stack],
            local_mem: CopyBytes {
                memory: caller_memory,
                destination: return_start,
                source: child_output,
                source_index: 0,
                remaining: Minimum(return_width, bytes::length(child_output)),
            },
            gas: caller_gas + child_gas,
            ..caller_frame
        },
    }
    where saved_world_state: WorldState;

    finish_static_call_revert: {
        k: [FinishStaticCall { return_start, return_width }, ..],
        call_stack: [
            caller_frame @ CallState {
                word_stack: caller_stack,
                local_mem: caller_memory,
                gas: caller_gas,
                ..
            },
            remaining_call_stack @ ..,
        ],
        interim_states: [
            SavedWorldState::Snapshot {
                account_id,
                balance,
                code,
                nonce,
                storage,
                original_storage,
                self_destruct,
                logs,
                refund,
                accessed_accounts,
                accessed_storage,
                created_accounts,
            },
            remaining_interim_states @ ..,
        ],
        account_id: _,
        balance: _,
        code: _,
        nonce: _,
        storage: _,
        original_storage: _,
        substate: _,
        output: child_output,
        status_code: Status::Reverted(),
        call_state: CallState { gas: child_gas, .. },
    } => {
        k: [Run(), ..],
        call_stack: remaining_call_stack,
        interim_states: remaining_interim_states,
        account_id,
        balance,
        code,
        nonce,
        storage,
        original_storage,
        substate: Substate {
            self_destruct,
            logs,
            refund,
            accessed_accounts,
            accessed_storage,
            created_accounts,
        },
        status_code: Status::Running(),
        call_state: CallState {
            word_stack: [0, ..caller_stack],
            local_mem: CopyBytes {
                memory: caller_memory,
                destination: return_start,
                source: child_output,
                source_index: 0,
                remaining: Minimum(return_width, bytes::length(child_output)),
            },
            gas: caller_gas + child_gas,
            ..caller_frame
        },
    };

    finish_static_call_exceptional_halt: {
        k: [FinishStaticCall { return_start, return_width }, ..],
        status_code: Status::StackUnderflow()
        | Status::StackOverflow()
        | Status::OutOfGas()
        | Status::BadJumpDestination()
        | Status::InvalidMemoryAccess()
        | Status::InvalidInstruction()
        | Status::StaticModeViolation(),
    } => {
        k: [FinishStaticCallExceptional { return_start, return_width }, ..],
    };

    finish_static_call_exception: {
        k: [FinishStaticCallExceptional { return_start, return_width }, ..],
        call_stack: [
            caller_frame @ CallState { word_stack: caller_stack, .. },
            remaining_call_stack @ ..,
        ],
        interim_states: [
            SavedWorldState::Snapshot {
                account_id,
                balance,
                code,
                nonce,
                storage,
                original_storage,
                self_destruct,
                logs,
                refund,
                accessed_accounts,
                accessed_storage,
                created_accounts,
            },
            remaining_interim_states @ ..,
        ],
        account_id: _,
        balance: _,
        code: _,
        nonce: _,
        storage: _,
        original_storage: _,
        substate: _,
        output: _,
        status_code: _,
        call_state: _,
    } => {
        k: [Run(), ..],
        call_stack: remaining_call_stack,
        interim_states: remaining_interim_states,
        account_id,
        balance,
        code,
        nonce,
        storage,
        original_storage,
        substate: Substate {
            self_destruct,
            logs,
            refund,
            accessed_accounts,
            accessed_storage,
            created_accounts,
        },
        output: bytes::empty(),
        status_code: Status::Running(),
        call_state: CallState { word_stack: [0, ..caller_stack], ..caller_frame },
    };

    #[k::requires(
        account > 9
            && (account != present_account
                || (account == present_account
                    && AccountEmpty { code, nonce, balance }))
    )]
    #[k::rule(owise)]
    exec_static_call_empty_or_absent: {
        k: [EnoughGas(StaticCall(), remaining), ..],
        account_id: present_account,
        balance,
        code,
        nonce,
        output: _,
        local_mem: memory,
        memory_used: used,
        accessed_accounts: accessed,
        word_stack: [
            gas_cap,
            account,
            argument_start,
            argument_width,
            return_start,
            return_width,
            ..,
        ],
        pc,
        gas: _,
    } => {
        k: [Run(), ..],
        output: bytes::empty(),
        memory_used: CallMemoryUsage {
            used,
            argument_start,
            argument_width,
            return_start,
            return_width,
        },
        accessed_accounts: MarkAccountAccess { accessed, account },
        word_stack: [1, ..],
        pc: pc + 1,
        gas: remaining,
    };

    exec_stop: {
        k: [EnoughGas(Stop(), remaining), ..],
        gas: _,
        output: _,
        status_code: _,
    } => {
        k: [..],
        gas: remaining,
        output: bytes::empty(),
        status_code: Status::Success(),
    };
}

k::rules! {
    for Machine;
    use GasResult::*;
    use Operation::*;

    stack_underflow_no_words_arithmetic: {
        k: [
            Add()
            | Mul()
            | Sub()
            | Div()
            | SignedDiv()
            | Mod()
            | SignedMod()
            | AddMod()
            | MulMod()
            | Exponent()
            | SignExtend(),
            ..,
        ],
        word_stack: [],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_underflow_no_words_comparison_bitwise: {
        k: [
            LessThan()
            | GreaterThan()
            | SignedLessThan()
            | SignedGreaterThan()
            | Equal()
            | IsZero()
            | BitAnd()
            | BitOr()
            | BitXor()
            | BitNot()
            | Byte()
            | ShiftLeft()
            | ShiftRight()
            | SignedShiftRight(),
            ..,
        ],
        word_stack: [],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_underflow_no_words_environment: {
        k: [
            AccountBalance()
            | ExternalCodeSize()
            | ExternalCodeHash()
            | ExternalCodeCopy()
            | CallDataLoad()
            | CallDataCopy()
            | CodeCopy()
            | ReturnDataCopy()
            | BlockHash(),
            ..,
        ],
        word_stack: [],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_underflow_no_words_memory_storage_control: {
        k: [
            MemoryLoad()
            | MemoryStore()
            | MemoryStore8()
            | Sha3()
            | StorageLoad()
            | StorageStore()
            | Jump()
            | JumpIf()
            | Return()
            | Revert(),
            ..,
        ],
        word_stack: [],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_underflow_one_word_arithmetic: {
        k: [
            Add()
            | Mul()
            | Sub()
            | Div()
            | SignedDiv()
            | Mod()
            | SignedMod()
            | AddMod()
            | MulMod()
            | Exponent()
            | SignExtend(),
            ..,
        ],
        word_stack: [_],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_underflow_one_word_comparison_bitwise: {
        k: [
            LessThan()
            | GreaterThan()
            | SignedLessThan()
            | SignedGreaterThan()
            | Equal()
            | BitAnd()
            | BitOr()
            | BitXor()
            | Byte()
            | ShiftLeft()
            | ShiftRight()
            | SignedShiftRight(),
            ..,
        ],
        word_stack: [_],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_underflow_one_word_environment_memory_control: {
        k: [
            ExternalCodeCopy()
            | CallDataCopy()
            | CodeCopy()
            | ReturnDataCopy()
            | MemoryStore()
            | MemoryStore8()
            | Sha3()
            | StorageStore()
            | JumpIf()
            | Return()
            | Revert(),
            ..,
        ],
        word_stack: [_],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_underflow_two_words: {
        k: [
            ExternalCodeCopy()
            | CallDataCopy()
            | CodeCopy()
            | ReturnDataCopy()
            | AddMod()
            | MulMod(),
            ..,
        ],
        word_stack: [_, _],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_underflow_three_words: {
        k: [ExternalCodeCopy(), ..],
        word_stack: [_, _, _],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_operation_underflow: {
        k: [StackUnderflowResult(), ..],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackUnderflow(),
    };

    stack_operation_overflow: {
        k: [StackOverflowResult(), ..],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StackOverflow(),
    };

    out_of_gas: {
        k: [InsufficientGas(), ..],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::OutOfGas(),
    };

    static_mode_violation: {
        k: [StaticViolationResult(), ..],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::StaticModeViolation(),
    };

    invalid_instruction: {
        k: [Invalid(), ..],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::InvalidInstruction(),
    };

    end_of_program: {
        k: [End(), ..],
        status_code: _,
    } => {
        k: [..],
        status_code: Status::Success(),
    };
}

k::claims! {
    for Machine;
    use ExecutionCommand::*;

    /// All-path claim spanning PUSH widths, ADD, PC observation, gas, and STOP.
    #[k::claim(all_paths)]
    push_add_pc_stop: {
        k: [Run()],
        program: k::bytes!(b"\x60\x02\x60\x03\x01\x58\x00"),
        address: 0,
        origin: 0,
        caller: 0,
        call_value: 0,
        call_data: k::bytes!(b""),
        gas_price: 0,
        output: k::bytes!(b""),
        local_mem: k::bytes!(b""),
        memory_used: 0,
        block_hashes: [],
        coinbase: 0,
        timestamp: 0,
        number: 0,
        prev_randao: 0,
        gas_limit: 0,
        chain_id: 0,
        base_fee: 0,
        word_stack: [],
        pc: 0,
        gas: 11,
        status_code: Status::Running(),
    } => {
        k: [],
        word_stack: [5, 5],
        pc: 6,
        gas: 0,
        status_code: Status::Success(),
    };

    /// All-path claim spanning the selected arithmetic and comparison tranches.
    #[k::claim(all_paths)]
    arithmetic_comparison_tranches_stop: {
        k: [Run()],
        program: k::bytes!(
            b"\x60\x02\x60\x07\x05\x60\x02\x60\x07\x07\x60\x05\x60\x06\x60\x04\x08\x60\x05\x60\x06\x60\x04\x09\x60\x07\x60\x02\x10\x60\x02\x60\x07\x11\x60\x07\x60\x02\x12\x60\x02\x60\x07\x13\x60\x05\x60\x05\x14\x60\x00\x15\x00",
        ),
        address: 0,
        origin: 0,
        caller: 0,
        call_value: 0,
        call_data: k::bytes!(b""),
        gas_price: 0,
        output: k::bytes!(b""),
        local_mem: k::bytes!(b""),
        memory_used: 0,
        block_hashes: [],
        coinbase: 0,
        timestamp: 0,
        number: 0,
        prev_randao: 0,
        gas_limit: 0,
        chain_id: 0,
        base_fee: 0,
        word_stack: [],
        pc: 0,
        gas: 107,
        status_code: Status::Running(),
    } => {
        k: [],
        word_stack: [1, 1, 1, 1, 1, 1, 4, 0, 1, 3],
        pc: 52,
        gas: 0,
        status_code: Status::Success(),
    };

    /// All-path claim spanning every Shanghai-active pure-word expression opcode.
    #[k::claim(all_paths)]
    pure_word_tranche_stop: {
        k: [Run()],
        program: k::bytes!(
            b"\x60\x08\x60\x02\x0a\x60\x80\x60\x00\x0b\x60\x0f\x60\x33\x16\x60\x0f\x60\x33\x17\x60\x0f\x60\x33\x18\x60\x00\x19\x61\xab\xcd\x60\x1e\x1a\x60\x03\x60\x04\x1b\x60\x80\x60\x03\x1c\x60\x00\x19\x60\x01\x1d\x00",
        ),
        address: 0,
        origin: 0,
        caller: 0,
        call_value: 0,
        call_data: k::bytes!(b""),
        gas_price: 0,
        output: k::bytes!(b""),
        local_mem: k::bytes!(b""),
        memory_used: 0,
        block_hashes: [],
        coinbase: 0,
        timestamp: 0,
        number: 0,
        prev_randao: 0,
        gas_limit: 0,
        chain_id: 0,
        base_fee: 0,
        word_stack: [],
        pc: 0,
        gas: 149,
        status_code: Status::Running(),
    } => {
        k: [],
        word_stack: [
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
            16,
            48,
            171,
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
            60,
            63,
            3,
            0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FF80,
            256,
        ],
        pc: 50,
        gas: 0,
        status_code: Status::Success(),
    };

    /// All-path claim spanning POP and depth-indexed DUP/SWAP execution.
    #[k::claim(all_paths)]
    stack_manipulation_stop: {
        k: [Run()],
        program: k::bytes!(b"\x60\x01\x60\x02\x60\x03\x82\x91\x50\x00"),
        address: 0,
        origin: 0,
        caller: 0,
        call_value: 0,
        call_data: k::bytes!(b""),
        gas_price: 0,
        output: k::bytes!(b""),
        local_mem: k::bytes!(b""),
        memory_used: 0,
        block_hashes: [],
        coinbase: 0,
        timestamp: 0,
        number: 0,
        prev_randao: 0,
        gas_limit: 0,
        chain_id: 0,
        base_fee: 0,
        word_stack: [],
        pc: 0,
        gas: 17,
        status_code: Status::Running(),
    } => {
        k: [],
        word_stack: [3, 1, 1],
        pc: 9,
        gas: 0,
        status_code: Status::Success(),
    };

    /// All-path claim spanning false and true JUMPI, JUMP, and JUMPDEST execution.
    #[k::claim(all_paths)]
    control_flow_tranche_stop: {
        k: [Run()],
        program: k::bytes!(
            b"\x60\x00\x60\xff\x57\x60\x01\x60\x0d\x57\xfe\xfe\xfe\x5b\x60\x12\x56\xfe\x5b\x00",
        ),
        address: 0,
        origin: 0,
        caller: 0,
        call_value: 0,
        call_data: k::bytes!(b""),
        gas_price: 0,
        output: k::bytes!(b""),
        local_mem: k::bytes!(b""),
        memory_used: 0,
        block_hashes: [],
        coinbase: 0,
        timestamp: 0,
        number: 0,
        prev_randao: 0,
        gas_limit: 0,
        chain_id: 0,
        base_fee: 0,
        word_stack: [],
        pc: 0,
        gas: 45,
        status_code: Status::Running(),
    } => {
        k: [],
        pc: 19,
        gas: 0,
        status_code: Status::Success(),
    };

    /// All-path claim spanning Shanghai execution-context observations and block history.
    #[k::claim(all_paths)]
    execution_context_tranche_stop: {
        k: [Run()],
        program: k::bytes!(
            b"\x30\x32\x33\x34\x36\x38\x3a\x3d\x41\x42\x43\x44\x45\x46\x48\x60\x10\x40\x5a\x00",
        ),
        address: 10,
        origin: 11,
        caller: 12,
        call_value: 13,
        call_data: k::bytes!(b"\xaa\xbb\xcc"),
        gas_price: 14,
        output: k::bytes!(b"\xdd\xee"),
        local_mem: k::bytes!(b""),
        memory_used: 0,
        block_hashes: [99, 0],
        coinbase: 15,
        timestamp: 16,
        number: 17,
        prev_randao: 18,
        gas_limit: 19,
        chain_id: 20,
        base_fee: 21,
        word_stack: [],
        pc: 0,
        gas: 55,
        status_code: Status::Running(),
    } => {
        k: [],
        output: k::bytes!(b""),
        word_stack: [0, 99, 21, 20, 19, 18, 17, 16, 15, 2, 14, 20, 3, 13, 12, 11, 10],
        pc: 19,
        gas: 0,
        status_code: Status::Success(),
    };

    /// All-path claim spanning memory writes, reads, size observation, and STOP.
    #[k::claim(all_paths)]
    memory_tranche_stop: {
        k: [Run()],
        program: k::bytes!(b"\x60\xaa\x60\x00\x52\x60\x00\x51\x59\x00"),
        address: 0,
        origin: 0,
        caller: 0,
        call_value: 0,
        call_data: k::bytes!(b""),
        gas_price: 0,
        output: k::bytes!(b"\xdd"),
        local_mem: k::bytes!(b""),
        memory_used: 0,
        block_hashes: [],
        coinbase: 0,
        timestamp: 0,
        number: 0,
        prev_randao: 0,
        gas_limit: 0,
        chain_id: 0,
        base_fee: 0,
        word_stack: [],
        pc: 0,
        gas: 20,
        status_code: Status::Running(),
    } => {
        k: [],
        output: k::bytes!(b""),
        local_mem: k::bytes!(
            b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xaa",
        ),
        memory_used: 1,
        word_stack: [32, 170],
        pc: 9,
        gas: 0,
        status_code: Status::Success(),
    };

    /// All-path claim spanning calldata load and all selected byte-copy sources.
    #[k::claim(all_paths)]
    load_copy_tranche_stop: {
        k: [Run()],
        program: k::bytes!(
            b"\x60\x00\x35\x60\x03\x60\x01\x60\x00\x37\x60\x02\x60\x00\x60\x03\x39\x60\x02\x60\x01\x60\x05\x3e\x00",
        ),
        address: 0,
        origin: 0,
        caller: 0,
        call_value: 0,
        call_data: k::bytes!(b"\xaa\xbb\xcc\xdd"),
        gas_price: 0,
        output: k::bytes!(b"\x11\x22\x33"),
        local_mem: k::bytes!(b""),
        memory_used: 0,
        block_hashes: [],
        coinbase: 0,
        timestamp: 0,
        number: 0,
        prev_randao: 0,
        gas_limit: 0,
        chain_id: 0,
        base_fee: 0,
        word_stack: [],
        pc: 0,
        gas: 54,
        status_code: Status::Running(),
    } => {
        k: [],
        output: k::bytes!(b""),
        local_mem: k::bytes!(
            b"\xbb\xcc\xdd\x60\x00\x22\x33\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        ),
        memory_used: 1,
        word_stack: [
            0xAABB_CCDD_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000,
        ],
        pc: 24,
        gas: 0,
        status_code: Status::Success(),
    };
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
    use krs_compiler::{emit_k, lower_descriptor_bundle, lower_semantic_theory};

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
        // `<<` and `^` stay operators until the semantic lowering chooses their domain.
        assert!(descriptors_json.contains(r#""application": "int_mod""#));
        assert!(descriptors_json.contains(r#""application": "int_pow_mod""#));
        assert!(descriptors_json.contains(r#""application": "shift_left""#));
        assert!(descriptors_json.contains(r#""application": "bit_xor""#));
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
                .contains("<account multiplicity=\"*\" type=\"Map\" initial=\"\">")
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

    /// The emitted rules whose left-hand side applies `name`: each rule's first line and its
    /// indented continuation lines (its side condition).
    fn rules_of<'a>(source: &'a str, name: &str) -> Vec<&'a str> {
        let head = format!("# {name} (");
        source
            .split("\n  rule ")
            .skip(1)
            .filter(|rule| rule.starts_with(&head))
            .map(|rule| {
                let end = rule
                    .match_indices('\n')
                    .find(|(index, _)| !rule[index + 1..].starts_with("    "))
                    .map_or(rule.len(), |(index, _)| index);
                &rule[..end]
            })
            .collect()
    }

    #[test]
    fn ecrec_applies_the_ecdsa_hook_only_to_recoverable_signatures() {
        let bundle = collect_host_descriptors_with_builtins(
            [package_context()],
            k::host_descriptors(),
            &k::builtin_registry(),
        )
        .expect("KEVM slice lowers");
        let semantic = lower_descriptor_bundle(&bundle).expect("KEVM descriptors lower");
        let definition = lower_semantic_theory(&semantic).expect("KEVM theory lowers");
        let source = emit_k(&definition).expect("KEVM definition emits");
        let source = source.source();
        let guard = "# kevmEcrecRecoverable ( # kevmBytesToInt ( # kevmReturnBytes ( Data:Bytes , 32 , 32 ) , 0 , 0 ) , # kevmBytesToInt ( # kevmReturnBytes ( Data:Bytes , 64 , 32 ) , 0 , 0 ) , # kevmBytesToInt ( # kevmReturnBytes ( Data:Bytes , 96 , 32 ) , 0 , 0 ) )";

        let outputs = rules_of(source, "kevmEcrecPrecompileOutput");
        assert_eq!(outputs.len(), 2, "{outputs:#?}");
        let (recovered, empty): (Vec<&str>, Vec<&str>) = outputs
            .iter()
            .copied()
            .partition(|rule| rule.contains("# kevmEcdsaRecover ("));
        assert_eq!(recovered.len(), 1, "{outputs:#?}");
        assert!(
            recovered[0].contains(&format!("\n    requires {guard} [label(")),
            "the ECDSA hook is applied without the recoverability guard: {}",
            recovered[0]
        );
        assert_eq!(empty.len(), 1, "{outputs:#?}");
        assert!(
            empty[0].starts_with("# kevmEcrecPrecompileOutput ( Data:Bytes ) => .Bytes\n"),
            "{}",
            empty[0]
        );
        assert!(
            empty[0].contains(&format!("\n    requires notBool {guard} [label(")),
            "{}",
            empty[0]
        );

        let n = "115792089237316195423570985008687907852837564279074904382605163141518161494337";
        let p = "115792089237316195423570985008687907853269984665640564039457584007908834671663";
        let recoverable = rules_of(source, "kevmEcrecRecoverable");
        assert_eq!(recoverable.len(), 1, "{recoverable:#?}");
        let body = recoverable[0];
        for conjunct in [
            "(V:Int ==Int 27) orElseBool (V:Int ==Int 28)".to_owned(),
            "0 <Int R:Int".to_owned(),
            format!("R:Int <Int {n}"),
            "0 <Int S:Int".to_owned(),
            format!("S:Int <Int {n}"),
            format!(
                "(((R:Int *Int R:Int) *Int R:Int) +Int 7) ^%Int (({p} -Int 1) /Int 2) {p}) ==Int 1"
            ),
        ] {
            assert!(body.contains(&conjunct), "missing `{conjunct}` in {body}");
        }
        assert!(!body.contains("requires"), "{body}");
    }
}
