//! Every K hook name the pinned k-rust knows, with its native capability.
//!
//! A quoted hook (`hook = "NAMESPACE.name"`) names a K hook that the typed
//! catalog ([`crate::HookOperation`]) does not cover. KRS cannot check its
//! signature, but it checks that the name exists: this table is the union of
//! the runtime and crypto hook classifications in k-rust's
//! `crates/k-rust/tests/fixtures/hook-capabilities.toml` (manifest version 2)
//! at the `Krs.lock` pin, without the structural hooks (`INT.Int`,
//! `MINT.literal`, ...), which never name an evaluator call. A sync test fails
//! when that file changes.
//!
//! A capability says whether k-rust has an evaluator, not whether a ground
//! application evaluates natively: an `EquationDefined` hook evaluates through
//! its prelude module's equations wherever that module is imported, and the
//! `BUFFER.*` hooks are unreachable on native-rust, which compiles
//! `STRING-BUFFER` as `STRING-BUFFER-IN-K` (upstream k-rust/buffer-hooks).

/// What the in-process k-rust backend does with a hooked function.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NativeHookCapability {
    /// k-rust evaluates the hook.
    Implemented,
    /// k-rust evaluates the hook only during ordinary execution, with its
    /// console state (`IO.write`, ...; upstream k-rust/console-write-through-execute).
    ExecutionOnly,
    /// k-rust has no evaluator for the hook, but the prelude module that
    /// declares it defines it by equations, which apply wherever that module
    /// is imported (`LIST.push`, `STRING.replace`, ...).
    EquationDefined,
    /// k-rust accepts the declaration, but neither an evaluator nor a prelude
    /// equation evaluates the hook.
    Unsupported,
}

impl NativeHookCapability {
    /// Lowercase name used in diagnostics.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Implemented => "implemented",
            Self::ExecutionOnly => "execution-only",
            Self::EquationDefined => "equation-defined",
            Self::Unsupported => "unsupported",
        }
    }
}

/// One pinned K hook name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RegisteredHook {
    /// Exact K spelling, `NAMESPACE.name`.
    pub name: &'static str,
    /// Native capability at the pin.
    pub capability: NativeHookCapability,
    /// Argument count of a crypto hook, from the pin's `[crypto.arities]`.
    pub crypto_arity: Option<u8>,
}

impl RegisteredHook {
    /// The namespace before the first `.`.
    #[must_use]
    pub fn namespace(&self) -> &'static str {
        self.name
            .split_once('.')
            .map_or(self.name, |(namespace, _)| namespace)
    }
}

/// Returns the pinned hook named `name`, if any.
#[must_use]
pub fn registered_hook(name: &str) -> Option<&'static RegisteredHook> {
    HOOK_REGISTRY
        .binary_search_by(|hook| hook.name.cmp(name))
        .ok()
        .map(|index| &HOOK_REGISTRY[index])
}

/// Returns the catalogued hook whose K spelling is `name`, if any.
#[must_use]
pub fn catalogued_hook(name: &str) -> Option<crate::HookOperation> {
    crate::HookOperation::ALL
        .into_iter()
        .find(|operation| operation.spec().k_hook == name)
}

const fn hook(
    name: &'static str,
    capability: NativeHookCapability,
    crypto_arity: Option<u8>,
) -> RegisteredHook {
    RegisteredHook {
        name,
        capability,
        crypto_arity,
    }
}

/// Every pinned hook name, sorted by name.
pub const HOOK_REGISTRY: &[RegisteredHook] = {
    use NativeHookCapability::{EquationDefined, ExecutionOnly, Implemented, Unsupported};
    &[
        hook("BOOL.and", Implemented, None),
        hook("BOOL.andThen", Implemented, None),
        hook("BOOL.eq", Implemented, None),
        hook("BOOL.implies", Implemented, None),
        hook("BOOL.ne", Implemented, None),
        hook("BOOL.not", Implemented, None),
        hook("BOOL.or", Implemented, None),
        hook("BOOL.orElse", Implemented, None),
        hook("BOOL.xor", Implemented, None),
        hook("BUFFER.concat", Unsupported, None),
        hook("BUFFER.empty", Unsupported, None),
        hook("BUFFER.toString", Unsupported, None),
        hook("BYTES.bytes2hex", Unsupported, None),
        hook("BYTES.bytes2int", Implemented, None),
        hook("BYTES.bytes2string", Implemented, None),
        hook("BYTES.concat", Implemented, None),
        hook("BYTES.decodeBytes", Implemented, None),
        hook("BYTES.empty", Implemented, None),
        hook("BYTES.encodeBytes", Implemented, None),
        hook("BYTES.get", Implemented, None),
        hook("BYTES.getMInt", Unsupported, None),
        hook("BYTES.int2bytes", Implemented, None),
        hook("BYTES.length", Implemented, None),
        hook("BYTES.lengthMInt", Unsupported, None),
        hook("BYTES.memset", Unsupported, None),
        hook("BYTES.padLeft", Implemented, None),
        hook("BYTES.padLeftMInt", Unsupported, None),
        hook("BYTES.padRight", Implemented, None),
        hook("BYTES.padRightMInt", Unsupported, None),
        hook("BYTES.replaceAt", Implemented, None),
        hook("BYTES.replaceAtMInt", Unsupported, None),
        hook("BYTES.reverse", Implemented, None),
        hook("BYTES.string2bytes", Implemented, None),
        hook("BYTES.substr", Implemented, None),
        hook("BYTES.substrMInt", Unsupported, None),
        hook("BYTES.update", Implemented, None),
        hook("BYTES.updateMInt", Unsupported, None),
        hook("FLOAT.abs", Implemented, None),
        hook("FLOAT.acos", Unsupported, None),
        hook("FLOAT.add", Implemented, None),
        hook("FLOAT.asin", Unsupported, None),
        hook("FLOAT.atan", Unsupported, None),
        hook("FLOAT.atan2", Unsupported, None),
        hook("FLOAT.ceil", Implemented, None),
        hook("FLOAT.cos", Unsupported, None),
        hook("FLOAT.div", Implemented, None),
        hook("FLOAT.eq", Implemented, None),
        hook("FLOAT.exp", Unsupported, None),
        hook("FLOAT.exponent", Unsupported, None),
        hook("FLOAT.exponentBits", Implemented, None),
        hook("FLOAT.float2int", Implemented, None),
        hook("FLOAT.floor", Implemented, None),
        hook("FLOAT.ge", Implemented, None),
        hook("FLOAT.gt", Implemented, None),
        hook("FLOAT.int2float", Implemented, None),
        hook("FLOAT.isNaN", Implemented, None),
        hook("FLOAT.le", Implemented, None),
        hook("FLOAT.log", Unsupported, None),
        hook("FLOAT.lt", Implemented, None),
        hook("FLOAT.max", Implemented, None),
        hook("FLOAT.maxValue", Implemented, None),
        hook("FLOAT.min", Implemented, None),
        hook("FLOAT.minValue", Unsupported, None),
        hook("FLOAT.mul", Implemented, None),
        hook("FLOAT.neg", Implemented, None),
        hook("FLOAT.pow", Unsupported, None),
        hook("FLOAT.precision", Implemented, None),
        hook("FLOAT.rem", Unsupported, None),
        hook("FLOAT.root", Implemented, None),
        hook("FLOAT.round", Implemented, None),
        hook("FLOAT.sign", Implemented, None),
        hook("FLOAT.sin", Unsupported, None),
        hook("FLOAT.sub", Implemented, None),
        hook("FLOAT.tan", Unsupported, None),
        hook("FLOAT.trunc", Implemented, None),
        hook("HASH.keccak256", Implemented, Some(1)),
        hook("HASH.ripemd160", Implemented, Some(1)),
        hook("HASH.sha256", Implemented, Some(1)),
        hook("HASH.sha3_256", Implemented, Some(1)),
        hook("INT.abs", Implemented, None),
        hook("INT.add", Implemented, None),
        hook("INT.and", Implemented, None),
        hook("INT.bitRange", Implemented, None),
        hook("INT.ediv", Implemented, None),
        hook("INT.emod", Implemented, None),
        hook("INT.eq", Implemented, None),
        hook("INT.ge", Implemented, None),
        hook("INT.gt", Implemented, None),
        hook("INT.le", Implemented, None),
        hook("INT.log2", Implemented, None),
        hook("INT.lt", Implemented, None),
        hook("INT.max", Implemented, None),
        hook("INT.min", Implemented, None),
        hook("INT.mul", Implemented, None),
        hook("INT.ne", Implemented, None),
        hook("INT.not", Implemented, None),
        hook("INT.or", Implemented, None),
        hook("INT.pow", Implemented, None),
        hook("INT.powmod", Implemented, None),
        hook("INT.rand", Unsupported, None),
        hook("INT.shl", Implemented, None),
        hook("INT.shr", Implemented, None),
        hook("INT.signExtendBitRange", Implemented, None),
        hook("INT.srand", Unsupported, None),
        hook("INT.sub", Implemented, None),
        hook("INT.tdiv", Implemented, None),
        hook("INT.tmod", Implemented, None),
        hook("INT.xor", Implemented, None),
        hook("IO.accept", Unsupported, None),
        hook("IO.close", Unsupported, None),
        hook("IO.getc", ExecutionOnly, None),
        hook("IO.lock", Unsupported, None),
        hook("IO.log", Unsupported, None),
        hook("IO.logString", Implemented, None),
        hook("IO.mkstemp", Unsupported, None),
        hook("IO.open", Unsupported, None),
        hook("IO.putc", ExecutionOnly, None),
        hook("IO.read", ExecutionOnly, None),
        hook("IO.remove", Unsupported, None),
        hook("IO.seek", Unsupported, None),
        hook("IO.seekEnd", Unsupported, None),
        hook("IO.shutdownWrite", Unsupported, None),
        hook("IO.system", Unsupported, None),
        hook("IO.tell", Unsupported, None),
        hook("IO.time", Unsupported, None),
        hook("IO.traceTerm", Unsupported, None),
        hook("IO.unlock", Unsupported, None),
        hook("IO.write", ExecutionOnly, None),
        hook("KEQUAL.eq", Implemented, None),
        hook("KEQUAL.ite", Implemented, None),
        hook("KEQUAL.ne", Implemented, None),
        hook("KREFLECTION.argv", Unsupported, None),
        hook("KREFLECTION.configuration", Unsupported, None),
        hook("KREFLECTION.fresh", Unsupported, None),
        hook("KREFLECTION.getKLabel", Unsupported, None),
        hook("KREFLECTION.getenv", Unsupported, None),
        hook("KREFLECTION.kompiledDir", Unsupported, None),
        hook("KREFLECTION.printKORE", Unsupported, None),
        hook("KREFLECTION.sort", Unsupported, None),
        hook("KRYPTO.blake2b256", Unsupported, Some(1)),
        hook("KRYPTO.blake2b256raw", Unsupported, Some(1)),
        hook("KRYPTO.blake2compress", Unsupported, Some(1)),
        hook("KRYPTO.bls12G1Add", Unsupported, Some(2)),
        hook("KRYPTO.bls12G1InSubgroup", Unsupported, Some(1)),
        hook("KRYPTO.bls12G1Msm", Unsupported, Some(2)),
        hook("KRYPTO.bls12G1Mul", Unsupported, Some(2)),
        hook("KRYPTO.bls12G1OnCurve", Unsupported, Some(1)),
        hook("KRYPTO.bls12G2Add", Unsupported, Some(2)),
        hook("KRYPTO.bls12G2InSubgroup", Unsupported, Some(1)),
        hook("KRYPTO.bls12G2Msm", Unsupported, Some(2)),
        hook("KRYPTO.bls12G2Mul", Unsupported, Some(2)),
        hook("KRYPTO.bls12G2OnCurve", Unsupported, Some(1)),
        hook("KRYPTO.bls12MapFp2ToG2", Unsupported, Some(2)),
        hook("KRYPTO.bls12MapFpToG1", Unsupported, Some(1)),
        hook("KRYPTO.bls12PairingCheck", Unsupported, Some(2)),
        hook("KRYPTO.bn128add", Implemented, Some(2)),
        hook("KRYPTO.bn128ate", Implemented, Some(2)),
        hook("KRYPTO.bn128g2valid", Implemented, Some(1)),
        hook("KRYPTO.bn128mul", Implemented, Some(2)),
        hook("KRYPTO.bn128valid", Implemented, Some(1)),
        hook("KRYPTO.ecdsaPubKey", Implemented, Some(1)),
        hook("KRYPTO.ecdsaRecover", Implemented, Some(4)),
        hook("KRYPTO.ecdsaSign", Unsupported, Some(2)),
        hook("KRYPTO.ed25519verify", Unsupported, Some(3)),
        hook("KRYPTO.keccak256", Implemented, Some(1)),
        hook("KRYPTO.keccak256raw", Implemented, Some(1)),
        hook("KRYPTO.p256verify", Unsupported, Some(1)),
        hook("KRYPTO.ripemd160", Implemented, Some(1)),
        hook("KRYPTO.ripemd160raw", Implemented, Some(1)),
        hook("KRYPTO.sha256", Implemented, Some(1)),
        hook("KRYPTO.sha256raw", Implemented, Some(1)),
        hook("KRYPTO.sha3", Unsupported, Some(1)),
        hook("KRYPTO.sha3256", Implemented, Some(1)),
        hook("KRYPTO.sha3raw", Unsupported, Some(1)),
        hook("KRYPTO.sha512", Unsupported, Some(1)),
        hook("KRYPTO.sha512_256", Unsupported, Some(1)),
        hook("KRYPTO.sha512_256raw", Implemented, Some(1)),
        hook("KRYPTO.sha512raw", Unsupported, Some(1)),
        hook("KRYPTO.verifyKZGProof", Unsupported, Some(4)),
        hook("LIST.concat", Implemented, None),
        hook("LIST.element", Implemented, None),
        hook("LIST.fill", Unsupported, None),
        hook("LIST.get", Implemented, None),
        hook("LIST.getMInt", Unsupported, None),
        hook("LIST.in", Implemented, None),
        hook("LIST.make", Implemented, None),
        hook("LIST.push", EquationDefined, None),
        hook("LIST.range", Implemented, None),
        hook("LIST.size", Implemented, None),
        hook("LIST.sizeMInt", Unsupported, None),
        hook("LIST.unit", Implemented, None),
        hook("LIST.update", Implemented, None),
        hook("LIST.updateAll", Implemented, None),
        hook("LIST.updateMInt", Unsupported, None),
        hook("MAP.choice", Implemented, None),
        hook("MAP.concat", Implemented, None),
        hook("MAP.difference", Implemented, None),
        hook("MAP.element", Implemented, None),
        hook("MAP.in_keys", Implemented, None),
        hook("MAP.inclusion", Implemented, None),
        hook("MAP.keys", Implemented, None),
        hook("MAP.keys_list", Implemented, None),
        hook("MAP.lookup", Implemented, None),
        hook("MAP.lookupOrDefault", Implemented, None),
        hook("MAP.remove", Implemented, None),
        hook("MAP.removeAll", Implemented, None),
        hook("MAP.size", Implemented, None),
        hook("MAP.unit", Implemented, None),
        hook("MAP.update", Implemented, None),
        hook("MAP.updateAll", Implemented, None),
        hook("MAP.values", Implemented, None),
        hook("MINT.MInt2bytes", Unsupported, None),
        hook("MINT.add", Implemented, None),
        hook("MINT.and", Implemented, None),
        hook("MINT.ashr", Implemented, None),
        hook("MINT.bitwidth", Implemented, None),
        hook("MINT.bytes2MInt", Unsupported, None),
        hook("MINT.eq", Implemented, None),
        hook("MINT.integer", Implemented, None),
        hook("MINT.lshr", Implemented, None),
        hook("MINT.mul", Implemented, None),
        hook("MINT.ne", Implemented, None),
        hook("MINT.neg", Implemented, None),
        hook("MINT.not", Implemented, None),
        hook("MINT.or", Implemented, None),
        hook("MINT.pow", Unsupported, None),
        hook("MINT.round", Unsupported, None),
        hook("MINT.sdiv", Implemented, None),
        hook("MINT.sext", Unsupported, None),
        hook("MINT.sge", Implemented, None),
        hook("MINT.sgt", Implemented, None),
        hook("MINT.shl", Implemented, None),
        hook("MINT.sle", Implemented, None),
        hook("MINT.slt", Implemented, None),
        hook("MINT.smax", Unsupported, None),
        hook("MINT.smin", Unsupported, None),
        hook("MINT.srem", Implemented, None),
        hook("MINT.sub", Implemented, None),
        hook("MINT.svalue", Implemented, None),
        hook("MINT.udiv", Implemented, None),
        hook("MINT.uge", Implemented, None),
        hook("MINT.ugt", Implemented, None),
        hook("MINT.ule", Implemented, None),
        hook("MINT.ult", Implemented, None),
        hook("MINT.umax", Unsupported, None),
        hook("MINT.umin", Unsupported, None),
        hook("MINT.urem", Implemented, None),
        hook("MINT.uvalue", Implemented, None),
        hook("MINT.xor", Implemented, None),
        hook("RANGEMAP.choice", Unsupported, None),
        hook("RANGEMAP.concat", Unsupported, None),
        hook("RANGEMAP.difference", Unsupported, None),
        hook("RANGEMAP.elementRng", Unsupported, None),
        hook("RANGEMAP.find_range", Unsupported, None),
        hook("RANGEMAP.in_keys", Unsupported, None),
        hook("RANGEMAP.inclusion", Unsupported, None),
        hook("RANGEMAP.keys", Unsupported, None),
        hook("RANGEMAP.keys_list", Unsupported, None),
        hook("RANGEMAP.lookup", Unsupported, None),
        hook("RANGEMAP.lookupOrDefault", Unsupported, None),
        hook("RANGEMAP.removeAll", Unsupported, None),
        hook("RANGEMAP.removeRng", Unsupported, None),
        hook("RANGEMAP.size", Unsupported, None),
        hook("RANGEMAP.unit", Unsupported, None),
        hook("RANGEMAP.updateAll", Unsupported, None),
        hook("RANGEMAP.updateRng", Unsupported, None),
        hook("RANGEMAP.values", Unsupported, None),
        hook("SECP256K1.ecdsaRecover", Implemented, Some(4)),
        hook("SET.choice", Implemented, None),
        hook("SET.concat", Implemented, None),
        hook("SET.difference", Implemented, None),
        hook("SET.element", Implemented, None),
        hook("SET.in", Implemented, None),
        hook("SET.inclusion", Implemented, None),
        hook("SET.intersection", Implemented, None),
        hook("SET.list2set", Implemented, None),
        hook("SET.set2list", Implemented, None),
        hook("SET.size", Implemented, None),
        hook("SET.union", Implemented, None),
        hook("SET.unit", Implemented, None),
        hook("STRING.base2string", Implemented, None),
        hook("STRING.category", Unsupported, None),
        hook("STRING.chr", Implemented, None),
        hook("STRING.concat", Implemented, None),
        hook("STRING.countAllOccurrences", Implemented, None),
        hook("STRING.directionality", Unsupported, None),
        hook("STRING.eq", Implemented, None),
        hook("STRING.find", Implemented, None),
        hook("STRING.findChar", EquationDefined, None),
        hook("STRING.float2string", Unsupported, None),
        hook("STRING.floatFormat", Unsupported, None),
        hook("STRING.ge", Implemented, None),
        hook("STRING.gt", Implemented, None),
        hook("STRING.int2string", Implemented, None),
        hook("STRING.le", Implemented, None),
        hook("STRING.length", Implemented, None),
        hook("STRING.lt", Implemented, None),
        hook("STRING.ne", Implemented, None),
        hook("STRING.ord", Implemented, None),
        hook("STRING.replace", EquationDefined, None),
        hook("STRING.replaceAll", Implemented, None),
        hook("STRING.replaceFirst", EquationDefined, None),
        hook("STRING.rfind", Implemented, None),
        hook("STRING.rfindChar", EquationDefined, None),
        hook("STRING.string2base", Implemented, None),
        hook("STRING.string2float", Unsupported, None),
        hook("STRING.string2int", Implemented, None),
        hook("STRING.string2token", Implemented, None),
        hook("STRING.substr", Implemented, None),
        hook("STRING.token2string", Implemented, None),
        hook("STRING.uuid", Unsupported, None),
    ]
};
