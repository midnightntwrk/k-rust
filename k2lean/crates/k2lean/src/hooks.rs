//! The hook registry: which hand-written prelude definition implements each K hook.
//!
//! Selection is by hook name only (the `hook{}("...")` attribute of the KORE symbol); the
//! generator never looks at a symbol's K name to decide its meaning.

#[derive(Clone, Debug)]
pub struct HookImpl {
    /// The Lean function, applied to the arguments in KORE order.
    pub lean: &'static str,
    /// Whether it returns `Option` (the hook is undefined at some arguments).
    pub partial: bool,
}

pub fn lookup(hook: &str) -> Option<HookImpl> {
    let (lean, partial) = match hook {
        "INT.add" => ("KPrelude.IntHook.add", false),
        "INT.sub" => ("KPrelude.IntHook.sub", false),
        "INT.mul" => ("KPrelude.IntHook.mul", false),
        "INT.tdiv" => ("KPrelude.IntHook.tdiv", true),
        "INT.tmod" => ("KPrelude.IntHook.tmod", true),
        "INT.ediv" => ("KPrelude.IntHook.ediv", true),
        "INT.emod" => ("KPrelude.IntHook.emod", true),
        "INT.pow" => ("KPrelude.IntHook.pow", true),
        "INT.shl" => ("KPrelude.IntHook.shl", true),
        "INT.shr" => ("KPrelude.IntHook.shr", true),
        "INT.abs" => ("KPrelude.IntHook.abs", false),
        "INT.min" => ("KPrelude.IntHook.min", false),
        "INT.max" => ("KPrelude.IntHook.max", false),
        "INT.lt" => ("KPrelude.IntHook.lt", false),
        "INT.le" => ("KPrelude.IntHook.le", false),
        "INT.gt" => ("KPrelude.IntHook.gt", false),
        "INT.ge" => ("KPrelude.IntHook.ge", false),
        "INT.eq" => ("KPrelude.IntHook.eq", false),
        "INT.ne" => ("KPrelude.IntHook.ne", false),
        "BOOL.not" => ("KPrelude.BoolHook.not", false),
        // `andThenBool`/`orElseBool` differ from `andBool`/`orBool` only in evaluation order;
        // as functions on defined operands they are the same (matching logic is strict in ⊥,
        // and the generator binds every operand before applying a hook).
        "BOOL.and" | "BOOL.andThen" => ("KPrelude.BoolHook.and", false),
        "BOOL.or" | "BOOL.orElse" => ("KPrelude.BoolHook.or", false),
        "BOOL.xor" => ("KPrelude.BoolHook.xor", false),
        "BOOL.implies" => ("KPrelude.BoolHook.implies", false),
        "BOOL.eq" => ("KPrelude.BoolHook.eq", false),
        "BOOL.ne" => ("KPrelude.BoolHook.ne", false),
        "KEQUAL.eq" => ("KPrelude.KEqHook.eq", false),
        "KEQUAL.ne" => ("KPrelude.KEqHook.ne", false),
        "KEQUAL.ite" => ("KPrelude.KEqHook.ite", false),
        "MAP.unit" => ("KPrelude.MapHook.unit", false),
        "MAP.element" => ("KPrelude.MapHook.element", false),
        "MAP.concat" => ("KPrelude.MapHook.concat", true),
        "MAP.update" => ("KPrelude.MapHook.update", false),
        "MAP.lookup" => ("KPrelude.MapHook.lookup", true),
        "MAP.lookupOrDefault" => ("KPrelude.MapHook.lookupOrDefault", false),
        "MAP.remove" => ("KPrelude.MapHook.remove", false),
        "MAP.in_keys" => ("KPrelude.MapHook.inKeys", false),
        "MAP.size" => ("KPrelude.MapHook.size", false),
        // hooks that SIMPLE uses and kimp does not
        "MAP.difference" => ("KPrelude.MapHook.difference", false),
        "MAP.updateAll" => ("KPrelude.MapHook.updateAll", false),
        "MAP.removeAll" => ("KPrelude.MapHook.removeAll", false),
        "MAP.keys" => ("KPrelude.MapHook.keys", false),
        "MAP.keys_list" => ("KPrelude.MapHook.keysList", false),
        "MAP.values" => ("KPrelude.MapHook.values", false),
        "MAP.inclusion" => ("KPrelude.MapHook.inclusion", false),
        "MAP.choice" => ("KPrelude.MapHook.choice", true),
        "SET.unit" => ("KPrelude.SetHook.unit", false),
        "SET.element" => ("KPrelude.SetHook.element", false),
        "SET.concat" => ("KPrelude.SetHook.concat", true),
        "SET.in" => ("KPrelude.SetHook.inSet", false),
        "SET.difference" => ("KPrelude.SetHook.difference", false),
        "SET.union" => ("KPrelude.SetHook.union", false),
        "SET.intersection" => ("KPrelude.SetHook.intersection", false),
        "SET.inclusion" => ("KPrelude.SetHook.inclusion", false),
        "SET.size" => ("KPrelude.SetHook.size", false),
        "SET.choice" => ("KPrelude.SetHook.choice", true),
        "SET.list2set" => ("KPrelude.SetHook.ofListHook", false),
        "SET.set2list" => ("KPrelude.SetHook.toListHook", false),
        "LIST.unit" => ("KPrelude.ListHook.unit", false),
        "LIST.element" => ("KPrelude.ListHook.element", false),
        "LIST.concat" => ("KPrelude.ListHook.concat", false),
        "LIST.push" => ("KPrelude.ListHook.push", false),
        "LIST.size" => ("KPrelude.ListHook.size", false),
        "LIST.get" => ("KPrelude.ListHook.get", true),
        "LIST.update" => ("KPrelude.ListHook.update", true),
        "LIST.make" => ("KPrelude.ListHook.make", true),
        "LIST.range" => ("KPrelude.ListHook.range", true),
        "LIST.in" => ("KPrelude.ListHook.inList", false),
        "STRING.concat" => ("KPrelude.StringHook.concat", false),
        "STRING.length" => ("KPrelude.StringHook.length", false),
        "STRING.substr" => ("KPrelude.StringHook.substr", false),
        "STRING.find" => ("KPrelude.StringHook.find", true),
        "STRING.rfind" => ("KPrelude.StringHook.rfind", true),
        "STRING.findChar" => ("KPrelude.StringHook.findChar", true),
        "STRING.rfindChar" => ("KPrelude.StringHook.rfindChar", true),
        "STRING.chr" => ("KPrelude.StringHook.chr", true),
        "STRING.ord" => ("KPrelude.StringHook.ord", true),
        "STRING.string2int" => ("KPrelude.StringHook.toInt", true),
        "STRING.int2string" => ("KPrelude.StringHook.ofInt", false),
        "STRING.base2string" => ("KPrelude.StringHook.base2string", true),
        "STRING.string2base" => ("KPrelude.StringHook.string2base", true),
        "STRING.replaceAll" => ("KPrelude.StringHook.replaceAll", false),
        "STRING.replaceFirst" => ("KPrelude.StringHook.replaceFirst", false),
        "STRING.countAllOccurrences" => ("KPrelude.StringHook.countAllOccurrences", false),
        "STRING.eq" => ("KPrelude.StringHook.eq", false),
        "STRING.ne" => ("KPrelude.StringHook.ne", false),
        "STRING.lt" => ("KPrelude.StringHook.lt", false),
        "STRING.le" => ("KPrelude.StringHook.le", false),
        "STRING.gt" => ("KPrelude.StringHook.gt", false),
        "STRING.ge" => ("KPrelude.StringHook.ge", false),
        // a token's string and back: token sorts are structures over `String`
        "INT.and" => ("KPrelude.IntHook.land", false),
        "INT.or" => ("KPrelude.IntHook.lor", false),
        "INT.xor" => ("KPrelude.IntHook.lxor", false),
        "INT.not" => ("KPrelude.IntHook.lnot", false),
        "INT.log2" => ("KPrelude.IntHook.log2", true),
        "INT.bitRange" => ("KPrelude.IntHook.bitRange", true),
        "INT.signExtendBitRange" => ("KPrelude.IntHook.signExtendBitRange", true),
        "INT.powmod" => ("KPrelude.IntHook.powmod", true),
        "BYTES.empty" => ("KPrelude.BytesHook.empty", false),
        "BYTES.concat" => ("KPrelude.BytesHook.concat", false),
        "BYTES.length" => ("KPrelude.BytesHook.length", false),
        "BYTES.reverse" => ("KPrelude.BytesHook.reverse", false),
        "BYTES.substr" => ("KPrelude.BytesHook.substr", true),
        "BYTES.get" => ("KPrelude.BytesHook.get", true),
        "BYTES.update" => ("KPrelude.BytesHook.update", true),
        "BYTES.replaceAt" => ("KPrelude.BytesHook.replaceAt", true),
        "BYTES.padRight" => ("KPrelude.BytesHook.padRight", true),
        "BYTES.padLeft" => ("KPrelude.BytesHook.padLeft", true),
        "BYTES.memset" => ("KPrelude.BytesHook.memset", true),
        "BYTES.bytes2string" => ("KPrelude.BytesHook.toStringHook", false),
        "BYTES.string2bytes" => ("KPrelude.BytesHook.ofStringHook", true),
        _ => return None,
    };
    Some(HookImpl { lean, partial })
}

/// The implementation for a hooked symbol: by hook name, and for the impure namespaces (`IO`,
/// impure `KREFLECTION` and `INT.rand`) the undefined function of the symbol's arity (a closed
/// model has no outside world; see `KPrelude.IOHook`).
pub fn for_symbol(d: &crate::ir::SymbolDecl) -> Option<HookImpl> {
    let h = d.hook()?;
    if let Some(i) = lookup(&h) {
        return Some(i);
    }
    let impure = d.attrs.has("impure") || h.starts_with("IO.");
    if impure && d.args.len() <= 4 {
        let lean: &'static str = [
            "KPrelude.IOHook.undef0",
            "KPrelude.IOHook.undef1",
            "KPrelude.IOHook.undef2",
            "KPrelude.IOHook.undef3",
            "KPrelude.IOHook.undef4",
        ][d.args.len()];
        return Some(HookImpl {
            lean,
            partial: true,
        });
    }
    None
}

/// Implementations whose result type Lean cannot infer from the arguments: the generated code
/// ascribes their type.
pub fn needs_ascription(lean: &str) -> bool {
    lean.starts_with("KPrelude.IOHook.")
        || matches!(
            lean,
            "KPrelude.MapHook.choice"
                | "KPrelude.SetHook.choice"
                | "KPrelude.ListHook.get"
                | "KPrelude.ListHook.make"
        )
}

/// The Lean simp lemmas/definitions that unfold hook implementations (for generated proofs).
pub fn unfold_names() -> &'static [&'static str] {
    &[
        "KPrelude.IntHook.add",
        "KPrelude.IntHook.sub",
        "KPrelude.IntHook.mul",
        "KPrelude.IntHook.lt",
        "KPrelude.IntHook.le",
        "KPrelude.IntHook.gt",
        "KPrelude.IntHook.ge",
        "KPrelude.IntHook.eq",
        "KPrelude.IntHook.ne",
        "KPrelude.BoolHook.not",
        "KPrelude.BoolHook.and",
        "KPrelude.BoolHook.or",
        "KPrelude.BoolHook.xor",
        "KPrelude.BoolHook.implies",
        "KPrelude.BoolHook.eq",
        "KPrelude.BoolHook.ne",
        "KPrelude.KEqHook.eq",
        "KPrelude.KEqHook.ne",
        "KPrelude.KEqHook.ite",
    ]
}

/// Also the partial and less common hooks, for equation and simplification proofs.
pub fn eq_unfold_names() -> Vec<&'static str> {
    let mut v: Vec<&'static str> = unfold_names().to_vec();
    v.extend([
        "KPrelude.IntHook.tdiv",
        "KPrelude.IntHook.tmod",
        "KPrelude.IntHook.ediv",
        "KPrelude.IntHook.emod",
        "KPrelude.IntHook.pow",
        "KPrelude.IntHook.shl",
        "KPrelude.IntHook.shr",
        "KPrelude.IntHook.abs",
        "KPrelude.IntHook.min",
        "KPrelude.IntHook.max",
        // laws that need more than unfolding
        "KPrelude.IntHook.int_ediv_eq_tdiv_sub_emod",
        "KPrelude.IntHook.int_emod_eq_of_lt",
        "Int.tmod_eq_of_lt",
    ]);
    v
}
