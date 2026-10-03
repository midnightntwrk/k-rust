//! Declarative builtin and hook catalogs for the pinned K frontend.

use serde::{Deserialize, Serialize};

use crate::Bn128PointSignature;

/// A sort constraint in a hook's declared-point signature.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HookSortConstraint {
    /// An exact builtin sort.
    Builtin(BuiltinSort),
    /// Any definition-declared algebraic sort.
    Declared,
    /// The production's result sort.
    Result,
}

/// Location of a sort whose constructor a hook requires.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HookPointSortSource {
    /// The production's first nonterminal argument.
    FirstArgument,
    /// The production's result sort.
    Result,
    /// A declared sort with the constructor signature's expected name.
    Named,
}

/// A constructor requirement imposed by the native hook backend.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HookPointConstructor {
    /// Required point name and integer-coordinate signature.
    pub signature: Bn128PointSignature,
    /// Where the production selects the point sort.
    pub source: HookPointSortSource,
}

/// Production signature and constructor requirements for a hook.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HookSignature {
    /// A fixed signature consisting entirely of builtin sorts.
    Builtin {
        /// Exact builtin result sort.
        result_sort: BuiltinSort,
        /// Ordered builtin argument sorts.
        argument_sorts: &'static [BuiltinSort],
        /// Required constructors in validation order.
        point_constructors: &'static [HookPointConstructor],
    },
    /// A signature involving a definition-declared point sort.
    DeclaredPoint {
        /// Constraint on the production's result sort.
        result_sort: HookSortConstraint,
        /// Ordered constraints on the nonterminal argument sorts.
        argument_sorts: &'static [HookSortConstraint],
        /// Required constructors in validation order.
        point_constructors: &'static [HookPointConstructor],
    },
}

impl HookSignature {
    /// Returns the fixed builtin signature, if present.
    #[must_use]
    pub const fn builtin_signature(self) -> Option<(BuiltinSort, &'static [BuiltinSort])> {
        match self {
            Self::Builtin {
                result_sort,
                argument_sorts,
                ..
            } => Some((result_sort, argument_sorts)),
            Self::DeclaredPoint { .. } => None,
        }
    }

    /// Returns the constructor constraints in validation order.
    #[must_use]
    pub const fn point_constructors(self) -> &'static [HookPointConstructor] {
        match self {
            Self::Builtin {
                point_constructors, ..
            }
            | Self::DeclaredPoint {
                point_constructors, ..
            } => point_constructors,
        }
    }
}

/// Per-hook facts shared by the Rust facade and pinned K adapters.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HookOperationSpec {
    /// Rust module in an authored hook path.
    pub rust_module: &'static str,
    /// Rust hook name within the module.
    pub rust_name: &'static str,
    /// Exact native frontend hook spelling.
    pub k_hook: &'static str,
    /// Production signature and backend constructor constraints.
    pub signature: HookSignature,
}

#[doc(hidden)]
#[macro_export]
macro_rules! __krs_hook_operation_catalog {
    ($callback:path) => {
        $callback! {
            /// Raw 32-byte Keccak-256 digest (`KRYPTO.keccak256raw`).
            KryptoKeccak256Raw {
                rust_module: krypto,
                rust_name: keccak256_raw,
                k_hook: "KRYPTO.keccak256raw",
                signature: $crate::HookSignature::Builtin {
                    result_sort: $crate::BuiltinSort::Bytes,
                    argument_sorts: &[$crate::BuiltinSort::Bytes],
                    point_constructors: &[],
                }
            }
            /// Raw 32-byte SHA-256 digest (`KRYPTO.sha256raw`).
            KryptoSha256Raw {
                rust_module: krypto,
                rust_name: sha256_raw,
                k_hook: "KRYPTO.sha256raw",
                signature: $crate::HookSignature::Builtin {
                    result_sort: $crate::BuiltinSort::Bytes,
                    argument_sorts: &[$crate::BuiltinSort::Bytes],
                    point_constructors: &[],
                }
            }
            /// Raw 20-byte RIPEMD-160 digest (`KRYPTO.ripemd160raw`).
            KryptoRipemd160Raw {
                rust_module: krypto,
                rust_name: ripemd160_raw,
                k_hook: "KRYPTO.ripemd160raw",
                signature: $crate::HookSignature::Builtin {
                    result_sort: $crate::BuiltinSort::Bytes,
                    argument_sorts: &[$crate::BuiltinSort::Bytes],
                    point_constructors: &[],
                }
            }
            /// Recover 64-byte secp256k1 public-key coordinates (`KRYPTO.ecdsaRecover`).
            KryptoEcdsaRecover {
                rust_module: krypto,
                rust_name: ecdsa_recover,
                k_hook: "KRYPTO.ecdsaRecover",
                signature: $crate::HookSignature::Builtin {
                    result_sort: $crate::BuiltinSort::Bytes,
                    argument_sorts: &[$crate::BuiltinSort::Bytes, $crate::BuiltinSort::Int, $crate::BuiltinSort::Bytes, $crate::BuiltinSort::Bytes],
                    point_constructors: &[],
                }
            }
            /// Validate a concrete `alt_bn128` G1 point (`KRYPTO.bn128valid`).
            KryptoBn128Valid {
                rust_module: krypto,
                rust_name: bn128_valid,
                k_hook: "KRYPTO.bn128valid",
                signature: $crate::HookSignature::DeclaredPoint {
                    result_sort: $crate::HookSortConstraint::Builtin($crate::BuiltinSort::Bool),
                    argument_sorts: &[$crate::HookSortConstraint::Declared],
                    point_constructors: &[$crate::HookPointConstructor {
                        signature: $crate::Bn128PointSignature::G1,
                        source: $crate::HookPointSortSource::FirstArgument,
                    }],
                }
            }
            /// Add two concrete `alt_bn128` G1 points (`KRYPTO.bn128add`).
            KryptoBn128Add {
                rust_module: krypto,
                rust_name: bn128_add,
                k_hook: "KRYPTO.bn128add",
                signature: $crate::HookSignature::DeclaredPoint {
                    result_sort: $crate::HookSortConstraint::Declared,
                    argument_sorts: &[$crate::HookSortConstraint::Result, $crate::HookSortConstraint::Result],
                    point_constructors: &[$crate::HookPointConstructor {
                        signature: $crate::Bn128PointSignature::G1,
                        source: $crate::HookPointSortSource::Result,
                    }],
                }
            }
            /// Multiply a concrete `alt_bn128` G1 point by an integer (`KRYPTO.bn128mul`).
            KryptoBn128Mul {
                rust_module: krypto,
                rust_name: bn128_mul,
                k_hook: "KRYPTO.bn128mul",
                signature: $crate::HookSignature::DeclaredPoint {
                    result_sort: $crate::HookSortConstraint::Declared,
                    argument_sorts: &[$crate::HookSortConstraint::Result, $crate::HookSortConstraint::Builtin($crate::BuiltinSort::Int)],
                    point_constructors: &[$crate::HookPointConstructor {
                        signature: $crate::Bn128PointSignature::G1,
                        source: $crate::HookPointSortSource::Result,
                    }],
                }
            }
            /// Validate a concrete `alt_bn128` G2 point and subgroup membership (`KRYPTO.bn128g2valid`).
            KryptoBn128G2Valid {
                rust_module: krypto,
                rust_name: bn128_g2_valid,
                k_hook: "KRYPTO.bn128g2valid",
                signature: $crate::HookSignature::DeclaredPoint {
                    result_sort: $crate::HookSortConstraint::Builtin($crate::BuiltinSort::Bool),
                    argument_sorts: &[$crate::HookSortConstraint::Declared],
                    point_constructors: &[$crate::HookPointConstructor {
                        signature: $crate::Bn128PointSignature::G2,
                        source: $crate::HookPointSortSource::FirstArgument,
                    }],
                }
            }
            /// Test whether an `alt_bn128` pairing product is the target-group identity (`KRYPTO.bn128ate`).
            KryptoBn128Ate {
                rust_module: krypto,
                rust_name: bn128_ate,
                k_hook: "KRYPTO.bn128ate",
                signature: $crate::HookSignature::Builtin {
                    result_sort: $crate::BuiltinSort::Bool,
                    argument_sorts: &[$crate::BuiltinSort::List, $crate::BuiltinSort::List],
                    point_constructors: &[
                        $crate::HookPointConstructor {
                            signature: $crate::Bn128PointSignature::G1,
                            source: $crate::HookPointSortSource::Named,
                        },
                        $crate::HookPointConstructor {
                            signature: $crate::Bn128PointSignature::G2,
                            source: $crate::HookPointSortSource::Named,
                        },
                    ],
                }
            }
        }
    };
}

macro_rules! define_hook_operations {
    ($( $(#[$meta:meta])* $variant:ident {
        rust_module: $module:ident,
        rust_name: $name:ident,
        k_hook: $hook:literal,
        signature: $signature:expr
    })*) => {
        /// Exact backend hook identities selected by qualified KRS semantics.
        ///
        /// Authored Rust, descriptors, and IR carry only these closed identities;
        /// the native hook spelling is the `k_hook` field of [`HookOperationSpec`].
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
        #[serde(rename_all = "snake_case")]
        pub enum HookOperation {
            $($(#[$meta])* $variant,)*
        }

        impl HookOperation {
            /// Complete hook catalog in stable semantic order.
            pub const ALL: [Self; [$(stringify!($variant)),*].len()] = [$(Self::$variant),*];

            /// Returns the pinned hook specification.
            #[must_use]
            pub const fn spec(self) -> &'static HookOperationSpec {
                match self {
                    $(Self::$variant => {
                        const SPEC: HookOperationSpec = HookOperationSpec {
                            rust_module: stringify!($module),
                            rust_name: stringify!($name),
                            k_hook: $hook,
                            signature: $signature,
                        };
                        &SPEC
                    },)*
                }
            }

            /// Fixed builtin signature, when the hook does not operate on a
            /// definition-declared algebraic sort.
            #[must_use]
            pub const fn builtin_signature(self) -> Option<(BuiltinSort, &'static [BuiltinSort])> {
                self.spec().signature.builtin_signature()
            }
        }
    };
}

__krs_hook_operation_catalog!(define_hook_operations);

/// Per-sort facts shared by the Rust facade and pinned K adapters.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BuiltinSortSpec {
    /// Rust marker name under `k::builtin`.
    pub marker_name: &'static str,
    /// Sort name in K source.
    pub k_name: &'static str,
    /// K module supplying the sort and its operations.
    pub k_module: Option<&'static str>,
    /// K module imported by the printer when no operation of this sort is used.
    pub k_syntax_module: Option<&'static str>,
}

#[doc(hidden)]
#[macro_export]
macro_rules! __krs_builtin_sort_catalog {
    ($callback:path) => {
        $callback! {
            /// Sort of an ordered K computation sequence (`K` in source K).
            KSequence {
                marker_name: KSequence,
                k_name: "K",
                k_module: None,
                k_syntax_module: None
            }
            /// Arbitrary-precision integer domain from pinned module `INT`.
            Int {
                marker_name: Int,
                k_name: "Int",
                k_module: Some("INT"),
                k_syntax_module: Some("INT-SYNTAX")
            }
            /// Boolean domain from pinned module `BOOL`.
            Bool {
                marker_name: Bool,
                k_name: "Bool",
                k_module: Some("BOOL"),
                k_syntax_module: Some("BOOL-SYNTAX")
            }
            /// Finite map collection from pinned module `MAP`.
            Map {
                marker_name: Map,
                k_name: "Map",
                k_module: Some("MAP"),
                k_syntax_module: Some("MAP")
            }
            /// Identifier token domain from pinned module `ID-SYNTAX`.
            Id {
                marker_name: Id,
                k_name: "Id",
                k_module: Some("ID-SYNTAX"),
                k_syntax_module: Some("ID-SYNTAX")
            }
            /// Byte-string domain from pinned module `BYTES`.
            Bytes {
                marker_name: Bytes,
                k_name: "Bytes",
                k_module: Some("BYTES"),
                k_syntax_module: Some("BYTES")
            }
            /// String token domain from pinned module `STRING-SYNTAX`.
            String {
                marker_name: String,
                k_name: "String",
                k_module: Some("STRING-SYNTAX"),
                k_syntax_module: Some("STRING-SYNTAX")
            }
            /// Associative finite sequence domain from pinned module `LIST`.
            List {
                marker_name: List,
                k_name: "List",
                k_module: Some("LIST"),
                k_syntax_module: Some("LIST")
            }
            /// Associative, commutative finite set domain from pinned module `SET`.
            Set {
                marker_name: Set,
                k_name: "Set",
                k_module: Some("SET"),
                k_syntax_module: Some("SET")
            }
        }
    };
}

macro_rules! define_builtin_sorts {
    ($( $(#[$meta:meta])* $variant:ident {
        marker_name: $marker:ident,
        k_name: $name:literal,
        k_module: $module:expr,
        k_syntax_module: $syntax_module:expr
    })*) => {
        /// Frontend-neutral identities for K sorts supplied by the K language rather
        /// than declared as generated KRS symbols.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
        #[serde(rename_all = "snake_case")]
        pub enum BuiltinSort {
            $($(#[$meta])* $variant,)*
        }

        impl BuiltinSort {
            /// Complete IR catalog in stable semantic order.
            pub const ALL: [Self; [$(stringify!($variant)),*].len()] = [$(Self::$variant),*];

            /// Returns the pinned sort specification.
            #[must_use]
            pub const fn spec(self) -> &'static BuiltinSortSpec {
                match self {
                    $(Self::$variant => {
                        const SPEC: BuiltinSortSpec = BuiltinSortSpec {
                            marker_name: stringify!($marker),
                            k_name: $name,
                            k_module: $module,
                            k_syntax_module: $syntax_module,
                        };
                        &SPEC
                    },)*
                }
            }

            /// Name of the Rust marker type `k::builtin::<name>` that denotes this sort.
            #[must_use]
            pub const fn marker_name(self) -> &'static str {
                self.spec().marker_name
            }

            /// Name of this sort in K source.
            #[must_use]
            pub const fn k_name(self) -> &'static str {
                self.spec().k_name
            }
        }
    };
}

__krs_builtin_sort_catalog!(define_builtin_sorts);

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
