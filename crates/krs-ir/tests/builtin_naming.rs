//! Naming rule S1: every builtin catalog name derives from its K production.
//!
//! The test restates, independently of the catalog, the facts of each K
//! production that the catalog exposes (first terminal, `symbol(..)`, `hook(..)`,
//! and declaring module, all from the pinned K 7.1.337 `domains.md`) together
//! with the Rust name the S1 derivation table lists for it. A reference
//! implementation of the N1/N2 rules derives the module and name from the
//! facts, and the test requires the derivation, the table, and the catalog to
//! agree for every entry. There is no exception list.

use std::collections::BTreeMap;

use krs_ir::{
    BuiltinOperation, HookOperation, ListOperation, MapOperation, SetOperation, TermMapOperation,
};

/// One K production as `domains.md` declares it, and the name the table lists.
struct Production {
    /// The catalog's native label (or, for a hook-catalog entry, its hook).
    label: &'static str,
    /// The production's first terminal; `None` for juxtaposition.
    terminal: Option<&'static str>,
    /// The production's `symbol(..)` attribute, if it has one.
    symbol: Option<&'static str>,
    /// The production's `hook(..)` attribute, if it has one.
    hook: Option<&'static str>,
    /// The module of `domains.md` that declares the production.
    declared_in: &'static str,
    /// The Rust module and name the derivation table lists.
    expected: (&'static str, &'static str),
}

const fn production(
    label: &'static str,
    terminal: Option<&'static str>,
    symbol: Option<&'static str>,
    hook: Option<&'static str>,
    declared_in: &'static str,
    expected: (&'static str, &'static str),
) -> Production {
    Production {
        label,
        terminal,
        symbol,
        hook,
        declared_in,
        expected,
    }
}

/// A hook-catalog entry: its identifier is the hook's operation name.
const fn hook_entry(hook: &'static str, expected: (&'static str, &'static str)) -> Production {
    Production {
        label: hook,
        terminal: None,
        symbol: None,
        hook: Some(hook),
        declared_in: "",
        expected,
    }
}

#[rustfmt::skip]
const BUILTIN_OPERATIONS: &[Production] = &[
    production("_+Int_", Some("+Int"), Some("_+Int_"), Some("INT.add"), "INT-COMMON", ("int", "add")),
    production("_-Int_", Some("-Int"), Some("_-Int_"), Some("INT.sub"), "INT-COMMON", ("int", "sub")),
    production("_*Int_", Some("*Int"), Some("_*Int_"), Some("INT.mul"), "INT-COMMON", ("int", "mul")),
    production("_/Int_", Some("/Int"), Some("_/Int_"), Some("INT.tdiv"), "INT-COMMON", ("int", "div")),
    production("_modInt_", Some("modInt"), Some("_modInt_"), Some("INT.emod"), "INT-COMMON", ("int", "rem_euclid")),
    production("_^%Int__", Some("^%Int"), Some("_^%Int__"), Some("INT.powmod"), "INT-COMMON", ("int", "pow_mod")),
    production("log2Int(_)_INT-COMMON_Int_Int", Some("log2Int"), None, Some("INT.log2"), "INT-COMMON", ("int", "log2")),
    production("_>>Int_", Some(">>Int"), Some("_>>Int_"), Some("INT.shr"), "INT-COMMON", ("int", "shift_right")),
    production("_<<Int_", Some("<<Int"), Some("_<<Int_"), Some("INT.shl"), "INT-COMMON", ("int", "shift_left")),
    production("_&Int_", Some("&Int"), Some("_&Int_"), Some("INT.and"), "INT-COMMON", ("int", "bit_and")),
    production("_xorInt_", Some("xorInt"), Some("_xorInt_"), Some("INT.xor"), "INT-COMMON", ("int", "bit_xor")),
    production("_|Int_", Some("|Int"), Some("_|Int_"), Some("INT.or"), "INT-COMMON", ("int", "bit_or")),
    production("_>=Int_", Some(">=Int"), Some("_>=Int_"), Some("INT.ge"), "INT-COMMON", ("int", "ge")),
    production("_>Int_", Some(">Int"), Some("_>Int_"), Some("INT.gt"), "INT-COMMON", ("int", "gt")),
    production("_<=Int_", Some("<=Int"), Some("_<=Int_"), Some("INT.le"), "INT-COMMON", ("int", "le")),
    production("_<Int_", Some("<Int"), Some("_<Int_"), Some("INT.lt"), "INT-COMMON", ("int", "lt")),
    production("_==Int_", Some("==Int"), Some("_==Int_"), Some("INT.eq"), "INT-COMMON", ("int", "eq")),
    production("_=/=Int_", Some("=/=Int"), Some("_=/=Int_"), Some("INT.ne"), "INT-COMMON", ("int", "ne")),
    production("notBool_", Some("notBool"), Some("notBool_"), Some("BOOL.not"), "BOOL-COMMON", ("bool", "not")),
    production("_==Bool_", Some("==Bool"), Some("_==Bool_"), Some("BOOL.eq"), "BOOL-COMMON", ("bool", "eq")),
    production("_=/=Bool_", Some("=/=Bool"), Some("_=/=Bool_"), Some("BOOL.ne"), "BOOL-COMMON", ("bool", "ne")),
    production("_andBool_", Some("andBool"), Some("_andBool_"), Some("BOOL.and"), "BOOL-COMMON", ("bool", "and")),
    production("_orBool_", Some("orBool"), Some("_orBool_"), Some("BOOL.or"), "BOOL-COMMON", ("bool", "or")),
    production("lengthBytes(_)_BYTES-HOOKED_Int_Bytes", Some("lengthBytes"), None, Some("BYTES.length"), "BYTES-HOOKED", ("bytes", "length")),
    production("_[_]_BYTES-HOOKED_Int_Bytes_Int", Some("["), None, Some("BYTES.get"), "BYTES-HOOKED", ("bytes", "get")),
    production(".Bytes_BYTES-HOOKED_Bytes", Some(".Bytes"), None, Some("BYTES.empty"), "BYTES-HOOKED", ("bytes", "empty")),
    production("_[_<-_]_BYTES-HOOKED_Bytes_Bytes_Int_Int", Some("["), None, Some("BYTES.update"), "BYTES-HOOKED", ("bytes", "update")),
    production("padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int", Some("padRightBytes"), None, Some("BYTES.padRight"), "BYTES-HOOKED", ("bytes", "pad_right")),
    production("substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int", Some("substrBytes"), None, Some("BYTES.substr"), "BYTES-HOOKED", ("bytes", "substr")),
    production("_%Int_", Some("%Int"), Some("_%Int_"), Some("INT.tmod"), "INT-COMMON", ("int", "rem")),
    production("_divInt_", Some("divInt"), Some("_divInt_"), Some("INT.ediv"), "INT-COMMON", ("int", "div_euclid")),
    production("_^Int_", Some("^Int"), Some("_^Int_"), Some("INT.pow"), "INT-COMMON", ("int", "pow")),
    production("~Int_", Some("~Int"), Some("~Int_"), Some("INT.not"), "INT-COMMON", ("int", "bit_not")),
    production("minInt(_,_)_INT-COMMON_Int_Int_Int", Some("minInt"), None, Some("INT.min"), "INT-COMMON", ("int", "min")),
    production("maxInt(_,_)_INT-COMMON_Int_Int_Int", Some("maxInt"), None, Some("INT.max"), "INT-COMMON", ("int", "max")),
    production("absInt(_)_INT-COMMON_Int_Int", Some("absInt"), None, Some("INT.abs"), "INT-COMMON", ("int", "abs")),
    production("_dividesInt__INT-COMMON_Bool_Int_Int", Some("dividesInt"), None, None, "INT-COMMON", ("int", "divides")),
    production("bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int", Some("bitRangeInt"), None, Some("INT.bitRange"), "INT-COMMON", ("int", "bit_range")),
    production("signExtendBitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int", Some("signExtendBitRangeInt"), None, Some("INT.signExtendBitRange"), "INT-COMMON", ("int", "sign_extend_bit_range")),
    production("_xorBool_", Some("xorBool"), Some("_xorBool_"), Some("BOOL.xor"), "BOOL-COMMON", ("bool", "xor")),
    production("_impliesBool_", Some("impliesBool"), Some("_impliesBool_"), Some("BOOL.implies"), "BOOL-COMMON", ("bool", "implies")),
    production("_andThenBool_", Some("andThenBool"), Some("_andThenBool_"), Some("BOOL.andThen"), "BOOL-COMMON", ("bool", "and_then")),
    production("_orElseBool_", Some("orElseBool"), Some("_orElseBool_"), Some("BOOL.orElse"), "BOOL-COMMON", ("bool", "or_else")),
    production("_+Bytes__BYTES-HOOKED_Bytes_Bytes_Bytes", Some("+Bytes"), None, Some("BYTES.concat"), "BYTES-HOOKED", ("bytes", "concat")),
    production("padLeftBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int", Some("padLeftBytes"), None, Some("BYTES.padLeft"), "BYTES-HOOKED", ("bytes", "pad_left")),
    production("reverseBytes(_)_BYTES-HOOKED_Bytes_Bytes", Some("reverseBytes"), None, Some("BYTES.reverse"), "BYTES-HOOKED", ("bytes", "reverse")),
    production("replaceAtBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Bytes", Some("replaceAtBytes"), None, Some("BYTES.replaceAt"), "BYTES-HOOKED", ("bytes", "replace_at")),
    production("Int2Bytes(_,_,_)_BYTES-HOOKED_Bytes_Int_Int_Endianness", Some("Int2Bytes"), None, Some("BYTES.int2bytes"), "BYTES-HOOKED", ("bytes", "from_int")),
    production("Int2BytesNoLen", Some("Int2Bytes"), Some("Int2BytesNoLen"), None, "BYTES-HOOKED", ("bytes", "from_int_no_len")),
    production("Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness", Some("Bytes2Int"), None, Some("BYTES.bytes2int"), "BYTES-HOOKED", ("bytes", "to_int")),
    production("littleEndianBytes", Some("LE"), Some("littleEndianBytes"), None, "BYTES-HOOKED", ("bytes", "little_endian")),
    production("bigEndianBytes", Some("BE"), Some("bigEndianBytes"), None, "BYTES-HOOKED", ("bytes", "big_endian")),
    production("signedBytes", Some("Signed"), Some("signedBytes"), None, "BYTES-HOOKED", ("bytes", "signed")),
    production("unsignedBytes", Some("Unsigned"), Some("unsignedBytes"), None, "BYTES-HOOKED", ("bytes", "unsigned")),
    production("_+String__STRING-COMMON_String_String_String", Some("+String"), None, Some("STRING.concat"), "STRING-COMMON", ("string", "concat")),
    production("_==String__STRING-COMMON_Bool_String_String", Some("==String"), None, Some("STRING.eq"), "STRING-COMMON", ("string", "eq")),
    production("_=/=String__STRING-COMMON_Bool_String_String", Some("=/=String"), None, Some("STRING.ne"), "STRING-COMMON", ("string", "ne")),
    production("_<String__STRING-COMMON_Bool_String_String", Some("<String"), None, Some("STRING.lt"), "STRING-COMMON", ("string", "lt")),
    production("_<=String__STRING-COMMON_Bool_String_String", Some("<=String"), None, Some("STRING.le"), "STRING-COMMON", ("string", "le")),
    production("_>String__STRING-COMMON_Bool_String_String", Some(">String"), None, Some("STRING.gt"), "STRING-COMMON", ("string", "gt")),
    production("_>=String__STRING-COMMON_Bool_String_String", Some(">=String"), None, Some("STRING.ge"), "STRING-COMMON", ("string", "ge")),
    production("lengthString(_)_STRING-COMMON_Int_String", Some("lengthString"), None, Some("STRING.length"), "STRING-COMMON", ("string", "length")),
    production("substrString(_,_,_)_STRING-COMMON_String_String_Int_Int", Some("substrString"), None, Some("STRING.substr"), "STRING-COMMON", ("string", "substr")),
    production("findString(_,_,_)_STRING-COMMON_Int_String_String_Int", Some("findString"), None, Some("STRING.find"), "STRING-COMMON", ("string", "find")),
    production("chrChar(_)_STRING-COMMON_String_Int", Some("chrChar"), None, Some("STRING.chr"), "STRING-COMMON", ("string", "chr")),
    production("ordChar(_)_STRING-COMMON_Int_String", Some("ordChar"), None, Some("STRING.ord"), "STRING-COMMON", ("string", "ord")),
    production("Int2String(_)_STRING-COMMON_String_Int", Some("Int2String"), None, Some("STRING.int2string"), "STRING-COMMON", ("string", "from_int")),
    production("String2Int(_)_STRING-COMMON_Int_String", Some("String2Int"), None, Some("STRING.string2int"), "STRING-COMMON", ("string", "to_int")),
    production("Bool2String(_)_STRING-COMMON_String_Bool", Some("Bool2String"), None, None, "STRING-COMMON", ("string", "from_bool")),
    production("String2Bool(_)_STRING-COMMON_Bool_String", Some("String2Bool"), None, None, "STRING-COMMON", ("string", "to_bool")),
    production("String2Bytes(_)_BYTES-HOOKED_Bytes_String", Some("String2Bytes"), None, Some("BYTES.string2bytes"), "BYTES-HOOKED", ("bytes", "from_string")),
    production("Bytes2String(_)_BYTES-HOOKED_String_Bytes", Some("Bytes2String"), None, Some("BYTES.bytes2string"), "BYTES-HOOKED", ("bytes", "to_string")),
    production("_==K_", Some("==K"), Some("_==K_"), Some("KEQUAL.eq"), "K-EQUAL-SYNTAX", ("kequal", "eq")),
    production("_=/=K_", Some("=/=K"), Some("_=/=K_"), Some("KEQUAL.ne"), "K-EQUAL-SYNTAX", ("kequal", "ne")),
    production("ite", Some("#if"), Some("ite"), Some("KEQUAL.ite"), "K-EQUAL-SYNTAX", ("kequal", "ite")),
    production("_+Float__FLOAT_Float_Float_Float", Some("+Float"), None, Some("FLOAT.add"), "FLOAT", ("float", "add")),
    production("_-Float__FLOAT_Float_Float_Float", Some("-Float"), None, Some("FLOAT.sub"), "FLOAT", ("float", "sub")),
    production("_*Float__FLOAT_Float_Float_Float", Some("*Float"), None, Some("FLOAT.mul"), "FLOAT", ("float", "mul")),
    production("_/Float__FLOAT_Float_Float_Float", Some("/Float"), None, Some("FLOAT.div"), "FLOAT", ("float", "div")),
    production("--Float__FLOAT_Float_Float", Some("--Float"), None, Some("FLOAT.neg"), "FLOAT", ("float", "neg")),
    production("_==Float_", Some("==Float"), Some("_==Float_"), Some("FLOAT.eq"), "FLOAT", ("float", "eq")),
    production("_=/=Float__FLOAT_Bool_Float_Float", Some("=/=Float"), None, None, "FLOAT", ("float", "ne")),
    production("_<Float__FLOAT_Bool_Float_Float", Some("<Float"), None, Some("FLOAT.lt"), "FLOAT", ("float", "lt")),
    production("_<=Float__FLOAT_Bool_Float_Float", Some("<=Float"), None, Some("FLOAT.le"), "FLOAT", ("float", "le")),
    production("_>Float__FLOAT_Bool_Float_Float", Some(">Float"), None, Some("FLOAT.gt"), "FLOAT", ("float", "gt")),
    production("_>=Float__FLOAT_Bool_Float_Float", Some(">=Float"), None, Some("FLOAT.ge"), "FLOAT", ("float", "ge")),
    production("absFloat(_)_FLOAT_Float_Float", Some("absFloat"), None, Some("FLOAT.abs"), "FLOAT", ("float", "abs")),
    production("floorFloat(_)_FLOAT_Float_Float", Some("floorFloat"), None, Some("FLOAT.floor"), "FLOAT", ("float", "floor")),
    production("ceilFloat(_)_FLOAT_Float_Float", Some("ceilFloat"), None, Some("FLOAT.ceil"), "FLOAT", ("float", "ceil")),
    production("truncFloat(_)_FLOAT_Float_Float", Some("truncFloat"), None, Some("FLOAT.trunc"), "FLOAT", ("float", "trunc")),
    production("roundFloat(_,_,_)_FLOAT_Float_Float_Int_Int", Some("roundFloat"), None, Some("FLOAT.round"), "FLOAT", ("float", "round")),
    production("rootFloat(_,_)_FLOAT_Float_Float_Int", Some("rootFloat"), None, Some("FLOAT.root"), "FLOAT", ("float", "root")),
    production("sqrtFloat(_)_FLOAT_Float_Float", Some("sqrtFloat"), None, None, "FLOAT", ("float", "sqrt")),
    production("minFloat(_,_)_FLOAT_Float_Float_Float", Some("minFloat"), None, Some("FLOAT.min"), "FLOAT", ("float", "min")),
    production("maxFloat(_,_)_FLOAT_Float_Float_Float", Some("maxFloat"), None, Some("FLOAT.max"), "FLOAT", ("float", "max")),
    production("isNaN(_)_FLOAT_Bool_Float", Some("isNaN"), None, Some("FLOAT.isNaN"), "FLOAT", ("float", "is_nan")),
    production("isInfinite(_)_FLOAT_Bool_Float", Some("isInfinite"), None, None, "FLOAT", ("float", "is_infinite")),
    production("signFloat(_)_FLOAT_Bool_Float", Some("signFloat"), None, Some("FLOAT.sign"), "FLOAT", ("float", "sign")),
    production("precisionFloat(_)_FLOAT_Int_Float", Some("precisionFloat"), None, Some("FLOAT.precision"), "FLOAT", ("float", "precision")),
    production("exponentBitsFloat(_)_FLOAT_Int_Float", Some("exponentBitsFloat"), None, Some("FLOAT.exponentBits"), "FLOAT", ("float", "exponent_bits")),
    production("maxValueFloat(_,_)_FLOAT_Float_Int_Int", Some("maxValueFloat"), None, Some("FLOAT.maxValue"), "FLOAT", ("float", "max_value")),
    production("Int2Float(_,_,_)_FLOAT_Float_Int_Int_Int", Some("Int2Float"), None, Some("FLOAT.int2float"), "FLOAT", ("float", "from_int")),
    production("Float2Int(_)_FLOAT_Int_Float", Some("Float2Int"), None, Some("FLOAT.float2int"), "FLOAT", ("float", "to_int")),
];

#[rustfmt::skip]
const MAP_OPERATIONS: &[Production] = &[
    production(".Map", Some(".Map"), Some(".Map"), Some("MAP.unit"), "MAP", ("map", "empty")),
    production("_|->_", Some("|->"), Some("_|->_"), Some("MAP.element"), "MAP", ("map", "item")),
    production("Map:update", Some("["), Some("Map:update"), Some("MAP.update"), "MAP", ("map", "update")),
    production("Map:lookup", Some("["), Some("Map:lookup"), Some("MAP.lookup"), "MAP", ("map", "get")),
    production("_in_keys(_)_MAP_Bool_KItem_Map", Some("in_keys"), None, Some("MAP.in_keys"), "MAP", ("map", "in_keys")),
    production("_[_<-undef]", Some("["), Some("_[_<-undef]"), Some("MAP.remove"), "MAP", ("map", "remove")),
    production("removeAll(_,_)_MAP_Map_Map_Set", Some("removeAll"), None, Some("MAP.removeAll"), "MAP", ("map", "remove_all")),
    production("keys(_)_MAP_Set_Map", Some("keys"), None, Some("MAP.keys"), "MAP", ("map", "keys")),
    production("keys_list(_)_MAP_List_Map", Some("keys_list"), None, Some("MAP.keys_list"), "MAP", ("map", "keys_list")),
    production("values(_)_MAP_List_Map", Some("values"), None, Some("MAP.values"), "MAP", ("map", "values")),
    production("sizeMap", Some("size"), Some("sizeMap"), Some("MAP.size"), "MAP", ("map", "size")),
    production("updateMap(_,_)_MAP_Map_Map_Map", Some("updateMap"), None, Some("MAP.updateAll"), "MAP", ("map", "update_all")),
    production("Map:lookupOrDefault", Some("["), Some("Map:lookupOrDefault"), Some("MAP.lookupOrDefault"), "MAP", ("map", "get_or_default")),
    // Juxtaposition; `map![..]` uses it as the structural concatenation.
    production("_Map_", None, Some("_Map_"), Some("MAP.concat"), "MAP", ("map", "concat")),
];

#[rustfmt::skip]
const LIST_OPERATIONS: &[Production] = &[
    production(".List", Some(".List"), Some(".List"), Some("LIST.unit"), "LIST", ("list", "empty")),
    production("ListItem", Some("ListItem"), Some("ListItem"), Some("LIST.element"), "LIST", ("list", "item")),
    production("_List_", None, Some("_List_"), Some("LIST.concat"), "LIST", ("list", "concat")),
    production("List:get", Some("["), Some("List:get"), Some("LIST.get"), "LIST", ("list", "get")),
    production("List:set", Some("["), Some("List:set"), Some("LIST.update"), "LIST", ("list", "update")),
    production("sizeList", Some("size"), Some("sizeList"), Some("LIST.size"), "LIST", ("list", "size")),
    production("makeList(_,_)_LIST_List_Int_KItem", Some("makeList"), None, Some("LIST.make"), "LIST", ("list", "make")),
    production("List:range", Some("range"), Some("List:range"), Some("LIST.range"), "LIST", ("list", "range")),
    production("updateList(_,_,_)_LIST_List_List_Int_List", Some("updateList"), None, Some("LIST.updateAll"), "LIST", ("list", "update_all")),
    production("_inList_", Some("in"), Some("_inList_"), Some("LIST.in"), "LIST", ("list", "contains")),
];

#[rustfmt::skip]
const SET_OPERATIONS: &[Production] = &[
    production(".Set", Some(".Set"), Some(".Set"), Some("SET.unit"), "SET", ("set", "empty")),
    production("SetItem", Some("SetItem"), Some("SetItem"), Some("SET.element"), "SET", ("set", "item")),
    production("_Set_", None, Some("_Set_"), Some("SET.concat"), "SET", ("set", "concat")),
    production("_|Set__SET_Set_Set_Set", Some("|Set"), None, Some("SET.union"), "SET", ("set", "union")),
    production("Set:in", Some("in"), Some("Set:in"), Some("SET.in"), "SET", ("set", "contains")),
    production("Set:difference", Some("-Set"), Some("Set:difference"), Some("SET.difference"), "SET", ("set", "difference")),
    production("intersectSet(_,_)_SET_Set_Set_Set", Some("intersectSet"), None, Some("SET.intersection"), "SET", ("set", "intersect")),
    production("size(_)_SET_Int_Set", Some("size"), None, Some("SET.size"), "SET", ("set", "size")),
    production("_<=Set__SET_Bool_Set_Set", Some("<=Set"), None, Some("SET.inclusion"), "SET", ("set", "is_subset")),
    production("Set2List(_)_COLLECTIONS_List_Set", Some("Set2List"), None, Some("SET.set2list"), "COLLECTIONS", ("set", "to_list")),
    production("List2Set(_)_COLLECTIONS_Set_List", Some("List2Set"), None, Some("SET.list2set"), "COLLECTIONS", ("set", "from_list")),
];

#[rustfmt::skip]
const HOOK_OPERATIONS: &[Production] = &[
    hook_entry("KRYPTO.keccak256raw", ("krypto", "keccak256_raw")),
    hook_entry("KRYPTO.sha256raw", ("krypto", "sha256_raw")),
    hook_entry("KRYPTO.ripemd160raw", ("krypto", "ripemd160_raw")),
    hook_entry("KRYPTO.ecdsaRecover", ("krypto", "ecdsa_recover")),
    hook_entry("KRYPTO.bn128valid", ("krypto", "bn128_valid")),
    hook_entry("KRYPTO.bn128add", ("krypto", "bn128_add")),
    hook_entry("KRYPTO.bn128mul", ("krypto", "bn128_mul")),
    hook_entry("KRYPTO.bn128g2valid", ("krypto", "bn128_g2_valid")),
    hook_entry("KRYPTO.bn128ate", ("krypto", "bn128_ate")),
];

/// The sort words S1 drops from identifiers, longest first so that `MInt` wins over `Int`.
const SORT_WORDS: &[&str] = &[
    "StringBuffer",
    "String",
    "Bytes",
    "Float",
    "MInt",
    "Bool",
    "Char",
    "List",
    "Int",
    "Map",
    "Set",
];

const RUST_KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern",
    "false", "fn", "for", "gen", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut",
    "pub", "ref", "return", "self", "static", "struct", "super", "trait", "true", "try", "type",
    "unsafe", "use", "where", "while", "abstract", "become", "box", "do", "final", "macro",
    "override", "priv", "typeof", "unsized", "virtual", "yield",
];

/// The rule of N2 that named an entry; a fallback replaces a later rule's name on a collision.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Rule {
    NumericWord,
    HookWord,
    Identifier,
    Conversion,
}

/// N1: the module is the hook namespace, or the namespace of the declaring domain module.
fn module(production: &Production) -> String {
    if let Some(hook) = production.hook {
        let namespace = hook
            .split_once('.')
            .expect("hooks are NAMESPACE.operation")
            .0;
        return namespace.to_ascii_lowercase();
    }
    let domain = production.declared_in;
    let domain = ["-COMMON", "-HOOKED", "-SYNTAX", "-KORE"]
        .iter()
        .find_map(|suffix| domain.strip_suffix(suffix))
        .unwrap_or(domain);
    match domain {
        "K-EQUAL" => "kequal".to_owned(),
        "K-IO" => "io".to_owned(),
        domain => domain.to_ascii_lowercase(),
    }
}

/// The module whose sort a sort word names (rule (c)).
fn sort_module(sort: &str) -> String {
    sort.to_ascii_lowercase()
}

/// Snake case: split before an uppercase letter preceded by a lowercase letter or
/// a digit, and between a digit run and a following letter; then lowercase.
/// `NaN` is one word.
fn snake_case(identifier: &str) -> String {
    let identifier = identifier.replace("NaN", "Nan");
    let characters = identifier.chars().collect::<Vec<_>>();
    let mut output = String::new();
    for (index, &character) in characters.iter().enumerate() {
        if index > 0 {
            let previous = characters[index - 1];
            let upper_after_word = character.is_ascii_uppercase()
                && (previous.is_ascii_lowercase() || previous.is_ascii_digit());
            let letter_after_digits = character.is_ascii_alphabetic() && previous.is_ascii_digit();
            if (upper_after_word || letter_after_digits) && !output.ends_with('_') {
                output.push('_');
            }
        }
        output.push(character.to_ascii_lowercase());
    }
    output
}

fn is_alphanumeric(text: &str) -> bool {
    !text.is_empty()
        && text
            .chars()
            .all(|character| character.is_ascii_alphanumeric())
}

/// A terminal is symbolic when it holds a character outside `[A-Za-z0-9_]` other
/// than a leading `#`; juxtaposition has no terminal and is symbolic.
fn is_symbolic(terminal: Option<&str>) -> bool {
    terminal.is_none_or(|terminal| {
        terminal
            .strip_prefix('#')
            .unwrap_or(terminal)
            .chars()
            .any(|character| !(character.is_ascii_alphanumeric() || character == '_'))
    })
}

/// (a1): the operator word of a numeric terminal, keyed by the operator and its sort.
fn numeric_word(namespace: &str, terminal: &str) -> Option<&'static str> {
    let sort = match namespace {
        "int" => "Int",
        "float" => "Float",
        "mint" => "MInt",
        "bool" => "Bool",
        _ => return None,
    };
    let operator = terminal.strip_suffix(sort)?;
    let equality = match operator {
        "==" => Some("eq"),
        "=/=" => Some("ne"),
        _ => None,
    };
    if sort == "Bool" {
        return equality;
    }
    let ordering = match operator {
        "<" => Some("lt"),
        "<=" => Some("le"),
        ">" => Some("gt"),
        ">=" => Some("ge"),
        _ => None,
    };
    let arithmetic = match operator {
        "+" => Some("add"),
        "-" => Some("sub"),
        "*" => Some("mul"),
        "/" => Some("div"),
        "%" => Some("rem"),
        "^" => Some("pow"),
        "^%" => Some("pow_mod"),
        "<<" => Some("shift_left"),
        ">>" => Some("shift_right"),
        "&" => Some("bit_and"),
        "|" => Some("bit_or"),
        "~" => Some("bit_not"),
        "--" => Some("neg"),
        "xor" if sort == "Int" => Some("bit_xor"),
        _ => None,
    };
    equality.or(ordering).or(arithmetic)
}

/// (a2): the hook's operation name, with the closed list of renames.
fn hook_word(hook: &str) -> String {
    let (namespace, operation) = hook.split_once('.').expect("hooks are NAMESPACE.operation");
    match (namespace, operation) {
        (_, "unit") | ("BYTES", "empty") => "empty".to_owned(),
        (_, "element") => "item".to_owned(),
        ("MAP", "lookup") => "get".to_owned(),
        ("MAP", "lookupOrDefault") => "get_or_default".to_owned(),
        (_, "inclusion") => "is_subset".to_owned(),
        (_, operation) => snake_case(operation),
    }
}

/// Drops a sort word used as a prefix (followed by an uppercase letter) or as a suffix.
fn drop_sort_word(identifier: &str) -> &str {
    for word in SORT_WORDS {
        if let Some(rest) = identifier.strip_prefix(word)
            && rest.starts_with(|character: char| character.is_ascii_uppercase())
        {
            return rest;
        }
        if let Some(rest) = identifier.strip_suffix(word)
            && rest.ends_with(|character: char| {
                character.is_ascii_lowercase() || character.is_ascii_digit()
            })
        {
            return rest;
        }
    }
    identifier
}

/// (c): `A2B` with an optional suffix, where A and B are sort words.
fn conversion(identifier: &str, module: &str) -> Option<String> {
    let (from, rest) = identifier.split_once('2')?;
    let from = SORT_WORDS.iter().find(|word| **word == from)?;
    let to = SORT_WORDS.iter().find(|word| rest.starts_with(*word))?;
    let suffix = &rest[to.len()..];
    let name = if sort_module(to) == module {
        format!("from_{}", snake_case(from))
    } else if sort_module(from) == module {
        format!("to_{}", snake_case(to))
    } else {
        return None;
    };
    Some(if suffix.is_empty() {
        name
    } else {
        format!("{name}_{}", snake_case(suffix))
    })
}

/// N2 rules (a1)-(c), before collisions are resolved.
fn primary_name(production: &Production, module: &str) -> (String, Rule) {
    if production.declared_in.is_empty() {
        // A hook-catalog entry: (b) applies to the hook's operation name.
        let hook = production.hook.expect("hook-catalog entries have hooks");
        let operation = hook
            .split_once('.')
            .expect("hooks are NAMESPACE.operation")
            .1;
        return (snake_case(operation), Rule::Identifier);
    }
    if let Some(terminal) = production.terminal
        && let Some(word) = numeric_word(module, terminal)
    {
        return (word.to_owned(), Rule::NumericWord);
    }
    if matches!(
        module,
        "string" | "bytes" | "map" | "list" | "set" | "kequal"
    ) && is_symbolic(production.terminal)
        && let Some(hook) = production.hook
    {
        return (hook_word(hook), Rule::HookWord);
    }
    let identifier = production
        .symbol
        .filter(|symbol| is_alphanumeric(symbol))
        .or(production.terminal)
        .expect("a production without a terminal is juxtaposition, named by its hook");
    let identifier = identifier.strip_prefix('#').unwrap_or(identifier);
    if let Some(name) = conversion(identifier, module) {
        return (name, Rule::Conversion);
    }
    (snake_case(drop_sort_word(identifier)), Rule::Identifier)
}

/// (d): the Rust std method with identical semantics, else the hook's operation name.
fn fallback(production: &Production) -> String {
    let hook = production.hook.expect("a fallback entry has a hook");
    match hook {
        "INT.emod" => "rem_euclid".to_owned(),
        "INT.ediv" => "div_euclid".to_owned(),
        "SET.in" | "LIST.in" => "contains".to_owned(),
        hook => snake_case(
            hook.split_once('.')
                .expect("hooks are NAMESPACE.operation")
                .1,
        ),
    }
}

/// Derives every entry's (module, name), resolving keywords and collisions by (d).
fn derive(productions: &[&Production]) -> BTreeMap<&'static str, (String, String)> {
    let primaries = productions
        .iter()
        .map(|production| {
            let module = module(production);
            let (name, rule) = primary_name(production, &module);
            (production.label, module, name, rule)
        })
        .collect::<Vec<_>>();
    let mut derived = BTreeMap::new();
    for (production, (label, module, name, rule)) in productions.iter().zip(&primaries) {
        let taken_by_earlier_rule =
            primaries
                .iter()
                .any(|(other, other_module, other_name, other_rule)| {
                    other != label
                        && other_module == module
                        && other_name == name
                        && other_rule < rule
                });
        let name = if RUST_KEYWORDS.contains(&name.as_str()) || taken_by_earlier_rule {
            fallback(production)
        } else {
            name.clone()
        };
        assert!(
            derived.insert(*label, (module.clone(), name)).is_none(),
            "duplicate label {label}"
        );
    }
    derived
}

fn all_productions() -> Vec<&'static Production> {
    BUILTIN_OPERATIONS
        .iter()
        .chain(MAP_OPERATIONS)
        .chain(LIST_OPERATIONS)
        .chain(SET_OPERATIONS)
        .chain(HOOK_OPERATIONS)
        .collect()
}

#[test]
fn every_derived_name_matches_the_table_without_exceptions() {
    let productions = all_productions();
    let derived = derive(&productions);
    for production in &productions {
        let (module, name) = &derived[production.label];
        assert_eq!(
            (module.as_str(), name.as_str()),
            production.expected,
            "S1 derives {module}::{name} for {}",
            production.label
        );
    }
    let mut names = BTreeMap::new();
    for production in &productions {
        assert!(
            names
                .insert(production.expected, production.label)
                .is_none(),
            "two entries are named {:?}",
            production.expected
        );
    }
}

fn row<'a>(rows: &'a [Production], label: &str) -> &'a Production {
    let mut matches = rows.iter().filter(|production| production.label == label);
    let row = matches
        .next()
        .unwrap_or_else(|| panic!("no derivation row for {label}"));
    assert!(matches.next().is_none(), "two derivation rows for {label}");
    row
}

#[test]
fn every_catalog_entry_has_its_derived_name_and_hook() {
    for operation in BuiltinOperation::ALL {
        let spec = operation.spec();
        let production = row(BUILTIN_OPERATIONS, spec.k_label);
        assert_eq!(
            (spec.rust_module, spec.rust_name),
            production.expected,
            "{operation:?}"
        );
        assert_eq!(spec.k_hook, production.hook, "{operation:?}");
    }
    assert_eq!(BuiltinOperation::ALL.len(), BUILTIN_OPERATIONS.len());

    for operation in TermMapOperation::ALL {
        let spec = operation.spec();
        let production = row(MAP_OPERATIONS, spec.k_label);
        let marker = operation.facade_marker();
        assert_eq!(
            (marker.module, marker.name),
            production.expected,
            "{operation:?}"
        );
        assert_eq!(spec.k_hook, production.hook, "{operation:?}");
    }
    for operation in [MapOperation::Empty, MapOperation::Item] {
        let spec = operation.spec();
        assert_eq!(
            spec.k_hook,
            row(MAP_OPERATIONS, spec.k_label).hook,
            "{operation:?}"
        );
    }
    row(MAP_OPERATIONS, MapOperation::CONCATENATION.k_label);
    assert_eq!(MapOperation::ALL.len() + 1, MAP_OPERATIONS.len());

    for operation in ListOperation::ALL {
        let spec = operation.spec();
        let production = row(LIST_OPERATIONS, spec.k_label);
        let marker = operation.facade_marker();
        assert_eq!(
            (marker.module, marker.name),
            production.expected,
            "{operation:?}"
        );
        assert_eq!(spec.k_hook, production.hook, "{operation:?}");
    }
    assert_eq!(ListOperation::ALL.len(), LIST_OPERATIONS.len());

    for operation in SetOperation::ALL {
        let spec = operation.spec();
        let production = row(SET_OPERATIONS, spec.k_label);
        let marker = operation.facade_marker();
        assert_eq!(
            (marker.module, marker.name),
            production.expected,
            "{operation:?}"
        );
        assert_eq!(spec.k_hook, production.hook, "{operation:?}");
    }
    assert_eq!(SetOperation::ALL.len(), SET_OPERATIONS.len());

    for operation in HookOperation::ALL {
        let spec = operation.spec();
        let production = row(HOOK_OPERATIONS, spec.k_hook);
        assert_eq!(
            (spec.rust_module, spec.rust_name),
            production.expected,
            "{operation:?}"
        );
    }
    assert_eq!(HookOperation::ALL.len(), HOOK_OPERATIONS.len());
}

#[test]
fn snake_case_follows_the_rule_text() {
    for (identifier, expected) in [
        ("andThen", "and_then"),
        ("keys_list", "keys_list"),
        ("bn128g2valid", "bn128_g2_valid"),
        ("keccak256raw", "keccak256_raw"),
        ("isNaN", "is_nan"),
        ("log2", "log2"),
        ("signExtendBitRange", "sign_extend_bit_range"),
    ] {
        assert_eq!(snake_case(identifier), expected, "{identifier}");
    }
}
