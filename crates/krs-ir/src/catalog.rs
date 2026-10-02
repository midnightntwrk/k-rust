//! Declarative compiler-provided operation catalog for the pinned K frontend.

use serde::{Deserialize, Serialize};

use crate::BuiltinSort;

/// K application spelling and argument-rendering convention.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuiltinOperationNotation {
    /// Literal pieces interleaved with arguments rendered as builtin operands.
    /// There must be one more piece than the operation's argument count.
    Mixfix {
        /// Literal text before, between, and after the arguments.
        pieces: &'static [&'static str],
    },
    /// A comma-separated call whose arguments use ordinary term rendering.
    Call {
        /// Function name before the parenthesized arguments.
        name: &'static str,
    },
}

/// Per-operation facts shared by the Rust facade and pinned K adapters.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BuiltinOperationSpec {
    /// Rust module under `k::builtin`.
    pub rust_module: &'static str,
    /// Rust marker name within the builtin module.
    pub rust_name: &'static str,
    /// Human-readable operation description.
    pub description: &'static str,
    /// Exact native frontend K label.
    pub k_label: &'static str,
    /// Application spelling used by the K printer.
    pub k_notation: BuiltinOperationNotation,
    /// Ordered builtin argument sorts; their count defines the arity.
    pub argument_sorts: &'static [BuiltinSort],
    /// Exact builtin result sort.
    pub result_sort: BuiltinSort,
    /// Whether the operation is a K function that may root a simplifier lemma.
    pub functional: bool,
}

#[doc(hidden)]
#[macro_export]
macro_rules! __krs_builtin_operation_catalog {
    ($callback:path) => {
        $callback! {
            /// `_+Int_` (`INT.add`).
            IntAdd {
                rust_module: int,
                rust_name: add,
                description: "integer addition",
                k_label: "_+Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " +Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_-Int_` (`INT.sub`).
            IntSub {
                rust_module: int,
                rust_name: sub,
                description: "integer subtraction",
                k_label: "_-Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " -Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_*Int_` (`INT.mul`).
            IntMul {
                rust_module: int,
                rust_name: mul,
                description: "integer multiplication",
                k_label: "_*Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " *Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_/Int_`, truncating division (`INT.tdiv`).
            IntTDiv {
                rust_module: int,
                rust_name: div,
                description: "integer truncating division",
                k_label: "_/Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " /Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_modInt_`, Euclidean modulus (`INT.mod`).
            IntMod {
                rust_module: int,
                rust_name: modulo,
                description: "integer modulus",
                k_label: "_modInt_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " modInt ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_^%Int__`, modular exponentiation (`INT.powmod`).
            IntPowMod {
                rust_module: int,
                rust_name: pow_mod,
                description: "integer modular exponentiation",
                k_label: "_^%Int__",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " ^%Int ", " ", ""] },
                argument_sorts: [Int, Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `log2Int`, integer base-two logarithm (`INT.log2`).
            IntLog2 {
                rust_module: int,
                rust_name: log2,
                description: "integer base-two logarithm",
                k_label: "log2Int(_)_INT-COMMON_Int_Int",
                k_notation: $crate::BuiltinOperationNotation::Call { name: "log2Int" },
                argument_sorts: [Int],
                result_sort: Int,
                functional: true
            }
            /// `_>>Int_`, arithmetic right shift (`INT.shr`).
            IntShiftRight {
                rust_module: int,
                rust_name: shift_right,
                description: "integer right shift",
                k_label: "_>>Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " >>Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_<<Int_`, left shift (`INT.shl`).
            IntShiftLeft {
                rust_module: int,
                rust_name: shift_left,
                description: "integer left shift",
                k_label: "_<<Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " <<Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_&Int_`, two's-complement bitwise conjunction (`INT.and`).
            IntBitAnd {
                rust_module: int,
                rust_name: bit_and,
                description: "integer bitwise conjunction",
                k_label: "_&Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " &Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_xorInt_`, two's-complement bitwise exclusive disjunction (`INT.xor`).
            IntBitXor {
                rust_module: int,
                rust_name: bit_xor,
                description: "integer bitwise exclusive disjunction",
                k_label: "_xorInt_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " xorInt ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_|Int_`, two's-complement bitwise inclusive disjunction (`INT.or`).
            IntBitOr {
                rust_module: int,
                rust_name: bit_or,
                description: "integer bitwise inclusive disjunction",
                k_label: "_|Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " |Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Int,
                functional: true
            }
            /// `_>=Int_`.
            IntGreaterEqual {
                rust_module: int,
                rust_name: ge,
                description: "integer greater-than-or-equal comparison",
                k_label: "_>=Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " >=Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Bool,
                functional: true
            }
            /// `_>Int_`.
            IntGreater {
                rust_module: int,
                rust_name: gt,
                description: "integer greater-than comparison",
                k_label: "_>Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " >Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Bool,
                functional: true
            }
            /// `_<=Int_`.
            IntLessEqual {
                rust_module: int,
                rust_name: le,
                description: "integer less-than-or-equal comparison",
                k_label: "_<=Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " <=Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Bool,
                functional: true
            }
            /// `_<Int_`.
            IntLess {
                rust_module: int,
                rust_name: lt,
                description: "integer less-than comparison",
                k_label: "_<Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " <Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Bool,
                functional: true
            }
            /// `_==Int_`.
            IntEqual {
                rust_module: int,
                rust_name: eq,
                description: "integer equality",
                k_label: "_==Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " ==Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Bool,
                functional: true
            }
            /// `_=/=Int_`.
            IntNotEqual {
                rust_module: int,
                rust_name: ne,
                description: "integer inequality",
                k_label: "_=/=Int_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " =/=Int ", ""] },
                argument_sorts: [Int, Int],
                result_sort: Bool,
                functional: true
            }
            /// `notBool_`.
            BoolNot {
                rust_module: bool,
                rust_name: not,
                description: "Boolean negation",
                k_label: "notBool_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["notBool ", ""] },
                argument_sorts: [Bool],
                result_sort: Bool,
                functional: true
            }
            /// `_==Bool_`.
            BoolEqual {
                rust_module: bool,
                rust_name: eq,
                description: "Boolean equality",
                k_label: "_==Bool_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " ==Bool ", ""] },
                argument_sorts: [Bool, Bool],
                result_sort: Bool,
                functional: true
            }
            /// `_=/=Bool_`.
            BoolNotEqual {
                rust_module: bool,
                rust_name: ne,
                description: "Boolean inequality",
                k_label: "_=/=Bool_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " =/=Bool ", ""] },
                argument_sorts: [Bool, Bool],
                result_sort: Bool,
                functional: true
            }
            /// `_andBool_`.
            BoolAnd {
                rust_module: bool,
                rust_name: and,
                description: "Boolean conjunction",
                k_label: "_andBool_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " andBool ", ""] },
                argument_sorts: [Bool, Bool],
                result_sort: Bool,
                functional: true
            }
            /// `_orBool_`.
            BoolOr {
                rust_module: bool,
                rust_name: or,
                description: "Boolean disjunction",
                k_label: "_orBool_",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " orBool ", ""] },
                argument_sorts: [Bool, Bool],
                result_sort: Bool,
                functional: true
            }
            /// `lengthBytes` (`BYTES.length`).
            BytesLength {
                rust_module: bytes,
                rust_name: length,
                description: "byte-string length",
                k_label: "lengthBytes(_)_BYTES-HOOKED_Int_Bytes",
                k_notation: $crate::BuiltinOperationNotation::Call { name: "lengthBytes" },
                argument_sorts: [Bytes],
                result_sort: Int,
                functional: true
            }
            /// Byte lookup (`BYTES.get`).
            BytesGet {
                rust_module: bytes,
                rust_name: get,
                description: "byte lookup",
                k_label: "_[_]_BYTES-HOOKED_Int_Bytes_Int",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " [ ", " ]"] },
                argument_sorts: [Bytes, Int],
                result_sort: Int,
                functional: true
            }
            /// `.Bytes` (`BYTES.empty`).
            BytesEmpty {
                rust_module: bytes,
                rust_name: empty,
                description: "empty byte string",
                k_label: ".Bytes_BYTES-HOOKED_Bytes",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &[".Bytes"] },
                argument_sorts: [],
                result_sort: Bytes,
                functional: true
            }
            /// Byte update (`BYTES.update`).
            BytesUpdate {
                rust_module: bytes,
                rust_name: update,
                description: "byte update",
                k_label: "_[_<-_]_BYTES-HOOKED_Bytes_Bytes_Int_Int",
                k_notation: $crate::BuiltinOperationNotation::Mixfix { pieces: &["", " [ ", " <- ", " ]"] },
                argument_sorts: [Bytes, Int, Int],
                result_sort: Bytes,
                functional: true
            }
            /// Right padding (`BYTES.padRight`).
            BytesPadRight {
                rust_module: bytes,
                rust_name: pad_right,
                description: "byte-string right padding",
                k_label: "padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int",
                k_notation: $crate::BuiltinOperationNotation::Call { name: "padRightBytes" },
                argument_sorts: [Bytes, Int, Int],
                result_sort: Bytes,
                functional: true
            }
            /// Half-open byte substring extraction (`BYTES.substr`).
            BytesSubstring {
                rust_module: bytes,
                rust_name: substr,
                description: "byte substring",
                k_label: "substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int",
                k_notation: $crate::BuiltinOperationNotation::Call { name: "substrBytes" },
                argument_sorts: [Bytes, Int, Int],
                result_sort: Bytes,
                functional: true
            }
        }
    };
}

macro_rules! define_builtin_operations {
    ($( $(#[$meta:meta])* $variant:ident {
        rust_module: $module:ident,
        rust_name: $name:ident,
        description: $description:literal,
        k_label: $label:literal,
        k_notation: $notation:expr,
        argument_sorts: [$($argument:ident),* $(,)?],
        result_sort: $result:ident,
        functional: $functional:literal
    })*) => {
        /// Exact compiler-provided operation identities for the pinned K 7.1.337
        /// `INT`, `BOOL`, and selected `BYTES` builtins used by qualified semantics.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
        #[serde(rename_all = "snake_case")]
        pub enum BuiltinOperation {
            $($(#[$meta])* $variant,)*
        }

        impl BuiltinOperation {
            /// Complete protocol catalog in stable semantic order.
            pub const ALL: [Self; [$(stringify!($variant)),*].len()] = [$(Self::$variant),*];

            /// Returns the pinned operation specification.
            #[must_use]
            pub const fn spec(self) -> &'static BuiltinOperationSpec {
                match self {
                    $(Self::$variant => {
                        const SPEC: BuiltinOperationSpec = BuiltinOperationSpec {
                            rust_module: stringify!($module),
                            rust_name: stringify!($name),
                            description: $description,
                            k_label: $label,
                            k_notation: $notation,
                            argument_sorts: &[$(BuiltinSort::$argument),*],
                            result_sort: BuiltinSort::$result,
                            functional: $functional,
                        };
                        &SPEC
                    },)*
                }
            }

            /// Returns the exact result sort from the pinned builtin signature.
            #[must_use]
            pub const fn result_sort(self) -> BuiltinSort {
                self.spec().result_sort
            }

            /// Whether this pinned builtin is a K function and may root a simplifier lemma.
            #[must_use]
            pub const fn is_functional(self) -> bool {
                self.spec().functional
            }

            /// Returns the ordered argument sorts from the pinned builtin signature.
            #[must_use]
            pub const fn argument_sorts(self) -> &'static [BuiltinSort] {
                self.spec().argument_sorts
            }
        }

        const _: () = {
            $(if let BuiltinOperationNotation::Mixfix { pieces } = BuiltinOperation::$variant.spec().k_notation {
                assert!(pieces.len() == BuiltinOperation::$variant.spec().argument_sorts.len() + 1);
            })*
        };
    };
}

__krs_builtin_operation_catalog!(define_builtin_operations);
