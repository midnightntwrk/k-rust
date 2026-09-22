//! Author-facing Rust host types and registration for KRS definitions.
//!
//! Procedural macros eventually generate ordinary Rust declarations plus a
//! small host-descriptor factory. With the default `inventory` feature, the
//! factory is registered through [`__register_host_descriptor!`], and a
//! generated host collector obtains freshly owned descriptors from
//! `host_descriptors`. Without it, a whole-crate step writes an explicit
//! registration table per semantics crate, and the collector passes those
//! tables to [`host_descriptors_from`]. Registration order is deliberately
//! unspecified and has no semantic meaning.
//!
//! This crate exposes the process-local descriptor layer, not the stable
//! compiler protocol. In particular, compiler input is not obtainable here:
//!
//! ```compile_fail
//! use krs::DescriptorBundle;
//! ```
//!
//! Host descriptors can contain function pointers and build-local Rust type
//! identities, so they cannot cross a serialization boundary:
//!
//! ```compile_fail
//! fn require_serializable<T: serde::Serialize>() {}
//!
//! require_serializable::<krs::HostDescriptor>();
//! ```

use std::any::TypeId;
use std::marker::PhantomData;

pub use krs_ir::{
    AnchorPrecision, BuiltinOperation, BuiltinSort, ConfigurationCellDescriptor,
    ConfigurationDescriptorError, HookOperation, HostAuthoredAnchor,
    HostBuiltinOperationRegistration, HostBuiltinRegistry, HostBuiltinRegistryError,
    HostBuiltinSortRegistration, HostConfigurationDescriptor,
    HostConfigurationInitializerDescriptor, HostConfigurationVariableDescriptor,
    HostConstructorDescriptor, HostConstructorFieldDescriptor, HostDeclarationIdentity,
    HostDescriptor, HostDescriptorPayload, HostDescriptorReference, HostIdentityError, HostItemId,
    HostListOperationRegistration, HostMapOperationRegistration, HostPackageKey, HostProvenance,
    HostProvenanceError, HostRuleDescriptor, HostRuleParameterDescriptor,
    HostSetOperationRegistration, HostSortDescriptor, HostSourceAnchor, HostSourcePosition,
    HostTypeKey, HostTypeReference, ItemKind, ListOperation, MapOperation, ProtocolVersion,
    ProvenanceKey, RuleBindingError, SentenceKind, SetOperation,
};
pub use krs_ir::{
    DescriptorApplicationHeadClass, DescriptorAssociativitySentence, DescriptorFieldReference,
    DescriptorFormatFragment, DescriptorGroupReference, DescriptorLexicalPrecedence,
    DescriptorLiteral, DescriptorPrecedenceChain, DescriptorRuleCondition, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSimplification, DescriptorSimplificationPriority,
    FormatFragment, GroupAssociativity, HostApplicationIdentity, HostApplicationReference,
    HostApplicationTarget, HostCellTermField, HostContextAliasReference, HostEnumVariantKey,
    HostEnumVariantReference, HostEnumVariantReferenceError, HostGrammarDescriptor, HostProduction,
    HostProductionAttribute, HostProductionItem, HostProductionOwner, HostRuleCondition,
    HostSortReference, HostStructuredRuleDescriptor, HostTerm, HostTermArgument, ProductionFieldId,
    ProductionGroupId, ProtocolV6ShapeError, StrictnessKind, enum_variant_disambiguator,
};
// These protocol-v7 host contracts are reexported because downstream proc
// macro expansions must name them through the actual (possibly renamed) KRS
// facade dependency. Stable descriptor counterparts remain in `krs-ir`.
pub use krs_ir::protocol_v7::{
    CellWrapper, ClaimModality, DescriptorCellColor, DescriptorCellMultiplicity,
    DescriptorCellName, DescriptorCellType, DescriptorConfigurationRoot,
    DescriptorKSequenceNotation, HostCellDeclaration, HostCellDeclarationReference, HostCellField,
    HostCellIdentity, HostCellReference, HostClaim, HostClaimBinder, HostConfigurationDeclaration,
    HostConfigurationInitializer, HostConfigurationReference, HostConfigurationRule,
    HostConfigurationVariable, HostContextAlias, HostFixedConfiguration, HostInitializerCell,
    HostInitializerStateTerm, HostRuleBinding, HostRuleCells, ProtocolCellContent,
    ProtocolCellDeclaration, ProtocolCellField, ProtocolConfigurationInitializer,
    ProtocolConfigurationVariable, ProtocolContextAliasBinding, ProtocolContextAliasBindingKind,
    ProtocolInitializerCell, ProtocolInitializerCellContent, ProtocolInitializerStateTerm,
    ProtocolInitializerTerm, ProtocolKSequence, ProtocolKSequenceItem, ProtocolMap,
    ProtocolMapBody, ProtocolMapItem, ProtocolRuleBinding, ProtocolRuleBindingKind,
    ProtocolRuleCell, ProtocolRuleCells, ProtocolRuleFrame, ProtocolRuleKSequence,
    ProtocolRuleKSequenceItem, ProtocolRuleMap, ProtocolRuleMapBody, ProtocolRuleMapItem,
    ProtocolRuleStateTerm, ProtocolV7ShapeError,
};
pub use krs_ir::{
    DescriptorHeadRule, DescriptorHeadRuleBinding, DescriptorHeadRuleExtra,
    DescriptorHeadRuleResult, HostHeadRule, HostHeadRuleBinding, HostHeadRuleCellReference,
    HostHeadRuleExtra, HostHeadRuleResult, ProtocolHeadRuleBinding, ProtocolHeadRuleExtra,
    ProtocolHeadRuleResult,
};
pub use krs_macros::{
    alias, anonymous, associativity, bracket, bytes, cell, cells, claim, configuration,
    constructor, constructors, context_alias, ensures, equation, exists, fragment, function, id,
    init, k, map, or_bool, precedence, priority, requires, rule, rules, seqstrict, simplification,
    sort, sorts, strict, subsort, symbol, term, token,
};

/// Rust-resolved metadata for an unqualified constructor application in a
/// readable rule table.
///
/// This is a hidden proc-macro implementation seam. The const selector keeps
/// enum variants distinct after rustc has inferred their owning enum from the
/// author's lexical imports. Standalone constructor types implement every
/// selector.
#[doc(hidden)]
pub trait __KrsRuleApplication<const SELECTOR: u64>: 'static {
    /// Produces the exact host declaration target for the resolved Rust type.
    #[doc(hidden)]
    fn __krs_rule_application(authored_path: &str) -> HostApplicationTarget;
}

/// Resolves an unqualified readable-rule application from an inferred Rust
/// witness type.
#[doc(hidden)]
#[must_use]
pub fn __krs_resolve_rule_application<T, const SELECTOR: u64>(
    _witness: &Option<T>,
    authored_path: &str,
) -> HostApplicationTarget
where
    T: __KrsRuleApplication<SELECTOR>,
{
    T::__krs_rule_application(authored_path)
}

// Framework identities are ordinary readable sorts, requested lazily by a
// definition whose sort graph names either one. The invocation also emits
// `FRAMEWORK_FACTORIES` for explicit registration. Collection reparses this
// file and recognizes readable sort blocks by the final path segment `sorts`,
// so the framework variant is invoked under that name.
mod framework {
    pub(crate) use krs_macros::__framework_sorts as sorts;
}
framework::sorts! {
    KItem;
    KResult: KItem;
}

/// Intrinsic K sorts and operations used by the Rust authoring surface.
///
/// Operation names are ordinary tuple-struct constructors. Consequently,
/// rustc checks operand types and arity before KRS collection, and ordinary
/// Rust module/import aliases retain the operation's exact type identity:
///
/// ```
/// use krs as dialect;
/// use dialect::builtin::int as integer;
/// use integer::add as plus;
///
/// let application: plus = plus(integer::Int, integer::Int);
/// let _: integer::add = application;
/// ```
///
/// Wrong arity and wrong-sort operands are ordinary Rust errors:
///
/// ```compile_fail
/// use krs::builtin::int::{Int, add};
///
/// let _ = add(Int);
/// ```
///
/// ```compile_fail
/// use krs::builtin::{bool::Bool, int};
///
/// let _ = int::add(int::Int, Bool);
/// ```
pub mod builtin {
    /// Type-level spelling of K's computation sequence sort.
    ///
    /// This is a zero-sized authoring token, not a host representation of a K
    /// sequence. The compiler obtains meaning from descriptors emitted by
    /// `k!`, never by evaluating this value.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct KSequence;

    impl KSequence {
        /// Constructs the zero-sized result of a checked `k!` expansion.
        ///
        /// This is public only because procedural macro output in downstream
        /// crates must be able to name it.
        #[doc(hidden)]
        #[must_use]
        pub const fn __new() -> Self {
            Self
        }
    }

    /// Marker for K's lexical identifier sort from `ID-SYNTAX`.
    ///
    /// This value is never used as a host identifier. Rust paths to the marker
    /// let the collector resolve the closed builtin sort by `TypeId`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Id;

    /// Type-shaped marker for K's finite-map sort.
    ///
    /// `K` and `V` preserve useful Rust authoring information (for example
    /// `Map<Id, Term<dyn Value>>`) while KRS resolves the outer `Map` marker to
    /// K's unparameterized semantic `Map` sort. The value is zero-sized and is
    /// never evaluated as a Rust collection.
    ///
    /// The hidden constructor is the expansion target for a checked `map!`
    /// island. It remains public so an expansion in a renamed downstream
    /// dependency can construct the authoring shell:
    ///
    /// ```
    /// use krs as language;
    /// use language::{Term, builtin::{Id, Map}};
    ///
    /// trait Value {}
    /// let _: Map<Id, Term<dyn Value>> = Map::__new();
    /// ```
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Map<K = Id, V = ()> {
        marker: std::marker::PhantomData<fn() -> (K, V)>,
    }

    /// Ordinary finite-map term operations.
    pub mod map {
        use super::{Id, Map};

        /// Persistent update of one typed map entry.
        ///
        /// The generic defaults provide one stable marker identity for KRS's
        /// `TypeId` registry, while the tuple constructor retains a genuine
        /// three-operand Rust shape for direct authoring checks.
        ///
        /// ```compile_fail
        /// use krs::builtin::{Id, Map, map::update};
        ///
        /// let _ = update(Map::<Id, ()>::__new(), Id);
        /// ```
        ///
        /// ```compile_fail
        /// use krs::builtin::{Id, map::update};
        ///
        /// let _ = update(Id, Id, ());
        /// ```
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Update<K = Id, V = ()>(pub Map<K, V>, pub K, pub V);

        /// Partial lookup of one typed map entry.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Get<K = Id, V = ()>(pub Map<K, V>, pub K);

        /// Boolean key-membership test.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct InKeys<K = Id, V = ()>(pub K, pub Map<K, V>);

        pub use Get as get;
        pub use InKeys as in_keys;
        /// Readable function-shaped spelling of a persistent update.
        ///
        /// Re-exporting the tuple struct, instead of defining a wrapper
        /// function, preserves the same identity in Rust's type and value
        /// namespaces. Module, facade, and local aliases therefore remain
        /// exact KRS application heads.
        pub use Update as update;
    }

    impl<K, V> Map<K, V> {
        /// Constructs the zero-sized result of a checked `map!` expansion.
        ///
        /// This is public only so downstream procedural-macro output can name
        /// it; author code does not construct or execute host maps directly.
        #[doc(hidden)]
        #[must_use]
        pub const fn __new() -> Self {
            Self {
                marker: std::marker::PhantomData,
            }
        }
    }

    /// Type-shaped marker for K's associative builtin-list sort.
    ///
    /// `T` retains useful Rust authoring information while KRS resolves the
    /// outer marker to K's unparameterized semantic `List` sort.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct List<T = ()> {
        marker: std::marker::PhantomData<fn() -> T>,
    }

    impl<T> List<T> {
        /// Constructs the zero-sized authoring shell.
        #[doc(hidden)]
        #[must_use]
        pub const fn __new() -> Self {
            Self {
                marker: std::marker::PhantomData,
            }
        }
    }

    /// Ordinary operations from K's pinned `LIST` module.
    pub mod list {
        use super::{List, int::Int};

        /// Marker for `.List`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Empty;

        /// Marker for `ListItem(K)`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Item<T = ()>(pub T);

        /// Marker for associative list concatenation.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Concat<T = ()>(pub List<T>, pub List<T>);

        /// Marker for indexed lookup.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Get<T = ()>(pub List<T>, pub Int);

        /// Marker for persistent indexed update.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Update<T = ()>(pub List<T>, pub Int, pub T);

        /// Marker for `size(List)`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Size<T = ()>(pub List<T>);

        /// Marker for `makeList(length, value)`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Make<T = ()>(pub Int, pub T);

        /// Marker for `range(List, fromFront, fromBack)`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Range<T = ()>(pub List<T>, pub Int, pub Int);

        /// Marker for `updateList(List, index, replacement)`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct UpdateAll<T = ()>(pub List<T>, pub Int, pub List<T>);

        pub use Concat as concat;
        pub use Empty as empty;
        pub use Get as get;
        pub use Item as item;
        pub use Make as make;
        pub use Range as range;
        pub use Size as size;
        pub use Update as update;
        pub use UpdateAll as update_all;
    }

    /// Type-shaped marker for K's associative builtin-set sort.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Set<T = ()> {
        marker: std::marker::PhantomData<fn() -> T>,
    }

    impl<T> Set<T> {
        /// Constructs the zero-sized authoring shell.
        #[doc(hidden)]
        #[must_use]
        pub const fn __new() -> Self {
            Self {
                marker: std::marker::PhantomData,
            }
        }
    }

    /// Ordinary operations from K's pinned `SET` module.
    pub mod set {
        use super::Set;

        /// Marker for `.Set`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Empty;

        /// Marker for `SetItem(K)`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Item<T = ()>(pub T);

        /// Marker for associative set concatenation.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Concat<T = ()>(pub Set<T>, pub Set<T>);

        /// Marker for set membership.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Contains<T = ()>(pub T, pub Set<T>);

        pub use Concat as concat;
        pub use Contains as contains;
        pub use Empty as empty;
        pub use Item as item;
    }

    /// Builtin operations and sort marker from K's pinned `INT` domain.
    pub mod int {
        /// Host marker for K's arbitrary-precision `Int` sort.
        ///
        /// This is an authoring token, not a host integer value. Integer
        /// literals and symbolic bindings are interpreted by KRS term
        /// expansion and are never evaluated through this type.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Int;

        /// Marker for integer addition, with its Rust-checked operand shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Add(pub Int, pub Int);

        /// Marker for integer subtraction, with its Rust-checked operand shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Sub(pub Int, pub Int);

        /// Marker for integer multiplication, with its Rust-checked operand shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Mul(pub Int, pub Int);

        /// Marker for truncating integer division, with its Rust-checked operand shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Div(pub Int, pub Int);

        /// Marker for Euclidean integer modulus, with its Rust-checked operand shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Mod(pub Int, pub Int);

        /// Marker for modular integer exponentiation.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct PowMod(pub Int, pub Int, pub Int);

        /// Marker for the integer base-two logarithm.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Log2(pub Int);

        /// Marker for arithmetic integer right shift.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct ShiftRight(pub Int, pub Int);

        /// Marker for integer left shift.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct ShiftLeft(pub Int, pub Int);

        /// Marker for two's-complement integer bitwise conjunction.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct BitAnd(pub Int, pub Int);

        /// Marker for two's-complement integer bitwise exclusive disjunction.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct BitXor(pub Int, pub Int);

        /// Marker for two's-complement integer bitwise inclusive disjunction.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct BitOr(pub Int, pub Int);

        /// Marker for integer greater-than-or-equal comparison.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Ge(pub Int, pub Int);

        /// Marker for integer greater-than comparison.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Gt(pub Int, pub Int);

        /// Marker for integer less-than-or-equal comparison.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Le(pub Int, pub Int);

        /// Marker for integer less-than comparison.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Lt(pub Int, pub Int);

        /// Marker for integer equality.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Eq(pub Int, pub Int);

        /// Marker for integer inequality.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Ne(pub Int, pub Int);

        // A `use` alias preserves both Rust namespaces. Each lowercase name is
        // therefore callable in value position and usable in
        // `TypeId::of::<...>()` in type position.
        pub use self::Eq as eq;
        pub use Add as add;
        pub use BitAnd as bit_and;
        pub use BitOr as bit_or;
        pub use BitXor as bit_xor;
        pub use Div as div;
        pub use Ge as ge;
        pub use Gt as gt;
        pub use Le as le;
        pub use Log2 as log2;
        pub use Lt as lt;
        pub use Mod as modulo;
        pub use Mul as mul;
        pub use Ne as ne;
        pub use PowMod as pow_mod;
        pub use ShiftLeft as shift_left;
        pub use ShiftRight as shift_right;
        pub use Sub as sub;
    }

    /// Builtin operations and sort marker from K's pinned `BOOL` domain.
    pub mod bool {
        /// Host marker for K's `Bool` sort.
        ///
        /// This is an authoring token, not a host Boolean value. Boolean
        /// literals and symbolic bindings are interpreted by KRS term
        /// expansion and are never evaluated through this type.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Bool;

        /// Marker for Boolean negation, with its Rust-checked operand shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Not(pub Bool);

        /// Marker for Boolean equality, with its Rust-checked operand shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Eq(pub Bool, pub Bool);

        /// Marker for Boolean inequality, with its Rust-checked operand shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Ne(pub Bool, pub Bool);

        /// Marker for object-language Boolean disjunction.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Or(pub Bool, pub Bool);

        /// Marker for object-language Boolean conjunction.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct And(pub Bool, pub Bool);

        // See the integer family: these aliases preserve constructor and type
        // identity while exposing the idiomatic authored spelling.
        pub use self::Eq as eq;
        pub use And as and;
        pub use Ne as ne;
        pub use Not as not;
        pub use Or as or;
    }

    /// Builtin operations and sort marker from K's pinned `BYTES` domain.
    pub mod bytes {
        use super::int::Int;

        /// Host marker for K's `Bytes` sort.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Bytes;

        /// Marker for `lengthBytes`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Length(pub Bytes);

        /// Marker for byte lookup.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Get(pub Bytes, pub Int);

        /// Marker for `.Bytes`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Empty;

        /// Marker for byte update.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Update(pub Bytes, pub Int, pub Int);

        /// Marker for right padding.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct PadRight(pub Bytes, pub Int, pub Int);

        /// Marker for byte substring extraction over a half-open range.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct Substr(pub Bytes, pub Int, pub Int);

        pub use Empty as empty;
        pub use Get as get;
        pub use Length as length;
        pub use PadRight as pad_right;
        pub use Substr as substr;
        pub use Update as update;
    }

    /// Convenient root spelling of the builtin Boolean sort marker.
    pub use bool::Bool;
    /// Convenient root spelling of the builtin byte-string sort marker.
    pub use bytes::Bytes;
    /// Convenient root spelling of the builtin integer sort marker.
    pub use int::Int;
}

// Rust-side membership required by the framework sort hierarchy generated
// above. Object-language builtin membership remains owned by the compiler's
// builtin catalog; these impls only make downstream readable supertraits such
// as `ValueSort: KResultSort` honest Rust bounds.
impl KItemSort for builtin::Int {}
impl KResultSort for builtin::Int {}
impl KItemSort for builtin::Bool {}
impl KResultSort for builtin::Bool {}
impl KItemSort for builtin::Bytes {}
impl KResultSort for builtin::Bytes {}

fn k_sequence_builtin_key() -> TypeId {
    TypeId::of::<builtin::KSequence>()
}

fn int_builtin_key() -> TypeId {
    TypeId::of::<builtin::int::Int>()
}

fn bool_builtin_key() -> TypeId {
    TypeId::of::<builtin::bool::Bool>()
}

fn id_builtin_key() -> TypeId {
    TypeId::of::<builtin::Id>()
}

fn map_builtin_key() -> TypeId {
    TypeId::of::<builtin::Map>()
}

fn bytes_builtin_key() -> TypeId {
    TypeId::of::<builtin::Bytes>()
}

fn list_builtin_key() -> TypeId {
    TypeId::of::<builtin::List>()
}

fn set_builtin_key() -> TypeId {
    TypeId::of::<builtin::Set>()
}

macro_rules! builtin_operation_keys {
    ($(($function:ident, $marker:path)),+ $(,)?) => {
        $(
            fn $function() -> TypeId {
                TypeId::of::<$marker>()
            }
        )+
    };
}

builtin_operation_keys! {
    (int_add_builtin_key, builtin::int::add),
    (int_sub_builtin_key, builtin::int::sub),
    (int_mul_builtin_key, builtin::int::mul),
    (int_tdiv_builtin_key, builtin::int::div),
    (int_mod_builtin_key, builtin::int::modulo),
    (int_pow_mod_builtin_key, builtin::int::pow_mod),
    (int_log2_builtin_key, builtin::int::log2),
    (int_shift_right_builtin_key, builtin::int::shift_right),
    (int_shift_left_builtin_key, builtin::int::shift_left),
    (int_bit_and_builtin_key, builtin::int::bit_and),
    (int_bit_xor_builtin_key, builtin::int::bit_xor),
    (int_bit_or_builtin_key, builtin::int::bit_or),
    (int_ge_builtin_key, builtin::int::ge),
    (int_gt_builtin_key, builtin::int::gt),
    (int_le_builtin_key, builtin::int::le),
    (int_lt_builtin_key, builtin::int::lt),
    (int_eq_builtin_key, builtin::int::eq),
    (int_ne_builtin_key, builtin::int::ne),
    (bool_not_builtin_key, builtin::bool::not),
    (bool_eq_builtin_key, builtin::bool::eq),
    (bool_ne_builtin_key, builtin::bool::ne),
    (bool_and_builtin_key, builtin::bool::and),
    (bool_or_builtin_key, builtin::bool::or),
    (bytes_length_builtin_key, builtin::bytes::length),
    (bytes_get_builtin_key, builtin::bytes::get),
    (bytes_empty_builtin_key, builtin::bytes::empty),
    (bytes_update_builtin_key, builtin::bytes::update),
    (bytes_pad_right_builtin_key, builtin::bytes::pad_right),
    (bytes_substr_builtin_key, builtin::bytes::substr),
}

fn map_update_builtin_key() -> TypeId {
    TypeId::of::<builtin::map::update>()
}

fn map_get_builtin_key() -> TypeId {
    TypeId::of::<builtin::map::get>()
}

fn map_in_keys_builtin_key() -> TypeId {
    TypeId::of::<builtin::map::in_keys>()
}

macro_rules! list_operation_keys {
    ($(($function:ident, $marker:path)),+ $(,)?) => {
        $(
            fn $function() -> TypeId {
                TypeId::of::<$marker>()
            }
        )+
    };
}

list_operation_keys! {
    (list_empty_builtin_key, builtin::list::empty),
    (list_item_builtin_key, builtin::list::item),
    (list_concat_builtin_key, builtin::list::concat),
    (list_get_builtin_key, builtin::list::get),
    (list_update_builtin_key, builtin::list::update),
    (list_size_builtin_key, builtin::list::size),
    (list_make_builtin_key, builtin::list::make),
    (list_range_builtin_key, builtin::list::range),
    (list_update_all_builtin_key, builtin::list::update_all),
}

list_operation_keys! {
    (set_empty_builtin_key, builtin::set::empty),
    (set_item_builtin_key, builtin::set::item),
    (set_concat_builtin_key, builtin::set::concat),
    (set_contains_builtin_key, builtin::set::contains),
}

/// Constructs the complete process-local registry of builtin Rust markers.
///
/// The registry joins rustc-resolved [`TypeId`] values to closed semantic
/// identities. It is intentionally host-only: aliases resolve because they
/// retain `TypeId`, while neither authored path spellings nor build-local keys
/// cross the compiler protocol boundary.
///
/// The returned registry has one entry for every [`BuiltinSort::ALL`] and
/// [`BuiltinOperation::ALL`] member and passes [`HostBuiltinRegistry::validate`].
#[must_use]
#[allow(clippy::too_many_lines)] // Declares the complete closed facade registry in stable order.
pub fn builtin_registry() -> HostBuiltinRegistry {
    let sorts = [
        (
            BuiltinSort::KSequence,
            k_sequence_builtin_key as fn() -> TypeId,
        ),
        (BuiltinSort::Int, int_builtin_key as fn() -> TypeId),
        (BuiltinSort::Bool, bool_builtin_key as fn() -> TypeId),
        (BuiltinSort::Map, map_builtin_key as fn() -> TypeId),
        (BuiltinSort::Id, id_builtin_key as fn() -> TypeId),
        (BuiltinSort::Bytes, bytes_builtin_key as fn() -> TypeId),
        (BuiltinSort::List, list_builtin_key as fn() -> TypeId),
        (BuiltinSort::Set, set_builtin_key as fn() -> TypeId),
    ]
    .into_iter()
    .map(|(sort, key)| HostBuiltinSortRegistration {
        sort,
        target: HostTypeKey(key),
    })
    .collect();

    let operations = [
        (
            BuiltinOperation::IntAdd,
            int_add_builtin_key as fn() -> TypeId,
        ),
        (BuiltinOperation::IntSub, int_sub_builtin_key),
        (BuiltinOperation::IntMul, int_mul_builtin_key),
        (BuiltinOperation::IntTDiv, int_tdiv_builtin_key),
        (BuiltinOperation::IntMod, int_mod_builtin_key),
        (BuiltinOperation::IntPowMod, int_pow_mod_builtin_key),
        (BuiltinOperation::IntLog2, int_log2_builtin_key),
        (BuiltinOperation::IntShiftRight, int_shift_right_builtin_key),
        (BuiltinOperation::IntShiftLeft, int_shift_left_builtin_key),
        (BuiltinOperation::IntBitAnd, int_bit_and_builtin_key),
        (BuiltinOperation::IntBitXor, int_bit_xor_builtin_key),
        (BuiltinOperation::IntBitOr, int_bit_or_builtin_key),
        (BuiltinOperation::IntGreaterEqual, int_ge_builtin_key),
        (BuiltinOperation::IntGreater, int_gt_builtin_key),
        (BuiltinOperation::IntLessEqual, int_le_builtin_key),
        (BuiltinOperation::IntLess, int_lt_builtin_key),
        (BuiltinOperation::IntEqual, int_eq_builtin_key),
        (BuiltinOperation::IntNotEqual, int_ne_builtin_key),
        (BuiltinOperation::BoolNot, bool_not_builtin_key),
        (BuiltinOperation::BoolEqual, bool_eq_builtin_key),
        (BuiltinOperation::BoolNotEqual, bool_ne_builtin_key),
        (BuiltinOperation::BoolAnd, bool_and_builtin_key),
        (BuiltinOperation::BoolOr, bool_or_builtin_key),
        (BuiltinOperation::BytesLength, bytes_length_builtin_key),
        (BuiltinOperation::BytesGet, bytes_get_builtin_key),
        (BuiltinOperation::BytesEmpty, bytes_empty_builtin_key),
        (BuiltinOperation::BytesUpdate, bytes_update_builtin_key),
        (BuiltinOperation::BytesPadRight, bytes_pad_right_builtin_key),
        (BuiltinOperation::BytesSubstring, bytes_substr_builtin_key),
    ]
    .into_iter()
    .map(|(operation, key)| HostBuiltinOperationRegistration {
        operation,
        target: HostTypeKey(key),
    })
    .collect();

    let map_operations = [
        (
            MapOperation::Update,
            map_update_builtin_key as fn() -> TypeId,
        ),
        (MapOperation::Get, map_get_builtin_key),
        (MapOperation::InKeys, map_in_keys_builtin_key),
    ]
    .into_iter()
    .map(|(operation, key)| HostMapOperationRegistration {
        operation,
        target: HostTypeKey(key),
    })
    .collect();

    let list_operations = [
        (
            ListOperation::Empty,
            list_empty_builtin_key as fn() -> TypeId,
        ),
        (ListOperation::Item, list_item_builtin_key),
        (ListOperation::Concat, list_concat_builtin_key),
        (ListOperation::Get, list_get_builtin_key),
        (ListOperation::Update, list_update_builtin_key),
        (ListOperation::Size, list_size_builtin_key),
        (ListOperation::Make, list_make_builtin_key),
        (ListOperation::Range, list_range_builtin_key),
        (ListOperation::UpdateAll, list_update_all_builtin_key),
    ]
    .into_iter()
    .map(|(operation, key)| HostListOperationRegistration {
        operation,
        target: HostTypeKey(key),
    })
    .collect();

    let set_operations = [
        (SetOperation::Empty, set_empty_builtin_key as fn() -> TypeId),
        (SetOperation::Item, set_item_builtin_key),
        (SetOperation::Concat, set_concat_builtin_key),
        (SetOperation::Contains, set_contains_builtin_key),
    ]
    .into_iter()
    .map(|(operation, key)| HostSetOperationRegistration {
        operation,
        target: HostTypeKey(key),
    })
    .collect();

    HostBuiltinRegistry {
        sorts,
        operations,
        map_operations,
        list_operations,
        set_operations,
    }
}

/// Fixed configuration-cell wrappers used by explicit fixed-state definitions.
pub mod configuration {
    use std::marker::PhantomData;

    use crate::builtin::KSequence;

    /// Type-level spelling of one fixed leaf cell containing a term of `T`.
    ///
    /// This is an authoring marker, not a host container. Its constructor keeps
    /// declarative configuration initializers ordinary rustc-valid Rust while
    /// KRS records the structured initializer instead of executing it.
    ///
    /// ```
    /// use krs as language;
    /// use language::{Term, builtin::{Id, Map}, configuration::Cell};
    ///
    /// trait Value {}
    /// type Environment = Map<Id, Term<dyn Value>>;
    /// let _: Cell<Environment> = Cell::new(Environment::__new());
    /// ```
    ///
    /// The content type remains checked by rustc:
    ///
    /// ```compile_fail
    /// use krs::{Term, builtin::{Id, Map}, configuration::Cell};
    ///
    /// trait Value {}
    /// let _: Cell<Map<Id, Term<dyn Value>>> = Cell::new(Map::<Id, ()>::__new());
    /// ```
    pub struct Cell<T> {
        marker: PhantomData<fn() -> T>,
    }

    impl<T> Cell<T> {
        /// Wraps one checked fixed-cell initializer value.
        #[must_use]
        pub fn new(_contents: T) -> Self {
            Self {
                marker: PhantomData,
            }
        }
    }

    /// Type-level spelling of the standard computation cell.
    ///
    /// Like [`KSequence`], this is a zero-sized authoring value. Constructing
    /// it lets the associated initializer remain ordinary rustc-valid Rust;
    /// collection never executes that initializer.
    ///
    /// ```
    /// use krs as language;
    /// use language::{builtin::KSequence, configuration::KCell};
    ///
    /// let _: KCell<KSequence> = KCell::new(KSequence::__new());
    /// ```
    pub struct KCell<T> {
        marker: PhantomData<fn() -> T>,
    }

    impl KCell<KSequence> {
        /// Wraps one checked computation-sequence authoring expression.
        #[must_use]
        pub const fn new(_contents: KSequence) -> Self {
            Self {
                marker: PhantomData,
            }
        }
    }

    /// Opaque authoring type for a compiler-owned nested-cell term.
    ///
    /// Values are created only by [`crate::fragment!`]. The host type carries
    /// the nominal parent for rustc while KRS validates the actual child set
    /// against the collected fixed-configuration declaration.
    pub struct CellFragment<Parent> {
        marker: PhantomData<fn() -> Parent>,
    }

    impl<Parent> CellFragment<Parent> {
        /// Constructs the zero-sized result of a checked macro expansion.
        #[doc(hidden)]
        #[must_use]
        pub const fn __new() -> Self {
            Self {
                marker: PhantomData,
            }
        }
    }
}

/// A symbolic object-language term whose expected K sort is `S`.
///
/// `Term<S>` is only a type-shaped authoring annotation at this milestone. It
/// is not a host value, a Rust evaluator, or a promise that open K sorts use
/// Rust trait-object dispatch. The private zero-sized representation prevents
/// authors from accidentally constructing runtime terms before a term IR
/// exists.
pub struct Term<S: ?Sized> {
    marker: PhantomData<fn(&S)>,
}

/// Returns all host descriptors linked into this collector process.
///
/// Each yielded value is freshly constructed by a registered function, so
/// owned strings and vectors are legal descriptor data. The iterator follows
/// the registration mechanism's unspecified enumeration order. Collectors
/// must resolve and deterministically order descriptors by stable identity
/// before producing compiler input.
///
/// This entry point requires the default `inventory` feature. Collectors
/// built without it enumerate generated tables through
/// [`host_descriptors_from`].
#[cfg(feature = "inventory")]
pub fn host_descriptors() -> impl Iterator<Item = HostDescriptor> {
    let framework_requested = inventory::iter::<__private::FrameworkSortRequest>
        .into_iter()
        .any(|request| request.manifest_dir() != env!("CARGO_MANIFEST_DIR"));
    inventory::iter::<__private::HostRegistration>
        .into_iter()
        .map(__private::HostRegistration::make)
        .filter(|descriptor| framework_requested || !is_framework_sort_descriptor(descriptor))
        .collect::<Vec<_>>()
        .into_iter()
}

/// Returns the host descriptors listed by explicit registration tables.
///
/// Each table belongs to one semantics crate and is written by a whole-crate
/// step, because a procedural macro invocation cannot enumerate its sibling
/// invocations. The framework `KItem`/`KResult` descriptors are included when
/// some table from a crate other than `krs` requests them, matching
/// [`host_descriptors`]. As with that entry point, the enumeration order has
/// no semantic meaning; collectors order descriptors by stable identity.
///
/// This entry point needs no linker-section support and is available whether
/// or not the `inventory` feature is enabled.
pub fn host_descriptors_from(
    tables: &[&__private::RegistrationTable],
) -> impl Iterator<Item = HostDescriptor> {
    let framework_requested = tables
        .iter()
        .any(|table| table.requests_framework && table.manifest_dir != env!("CARGO_MANIFEST_DIR"));
    let mut registrar = __private::Registrar::default();
    if framework_requested {
        for factory in FRAMEWORK_FACTORIES {
            registrar.factory(*factory);
        }
    }
    for table in tables {
        (table.register)(&mut registrar);
    }
    registrar
        .into_factories()
        .into_iter()
        .map(|factory| factory())
        .collect::<Vec<_>>()
        .into_iter()
}

#[cfg(feature = "inventory")]
fn is_framework_sort_descriptor(descriptor: &HostDescriptor) -> bool {
    descriptor.id.package().cargo_name() == env!("CARGO_PKG_NAME")
        && descriptor.id.package().cargo_version() == env!("CARGO_PKG_VERSION")
        && descriptor.id.package().manifest_dir()
            == std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        && descriptor.id.rust_module_path() == [env!("CARGO_CRATE_NAME")]
        && descriptor.id.item_kind() == ItemKind::Sort
        && matches!(descriptor.id.item_name(), "KItem" | "KResult")
}

/// Registers a host-descriptor factory in the final collector binary.
///
/// This is a hidden expansion boundary for KRS procedural macros. Authors
/// should not call it directly. Macro expansion should resolve the actual
/// facade dependency name and invoke this macro through that path; `$crate`
/// then keeps the concrete linker-registration mechanism rename-safe.
///
/// The recorded factory path is census data for explicit-table generation;
/// it never enters a descriptor.
#[cfg(feature = "inventory")]
#[doc(hidden)]
#[macro_export]
macro_rules! __register_host_descriptor {
    ($factory:path $(,)?) => {
        $crate::__private::inventory::submit! {
            $crate::__private::HostRegistration::new(
                $factory,
                ::core::concat!(::core::module_path!(), "::", ::core::stringify!($factory)),
                ::core::env!("CARGO_MANIFEST_DIR"),
            )
        }
    };
}

/// Type-checks a host-descriptor factory without registering it.
///
/// Without the `inventory` feature, the crate's explicit registration table
/// lists the factory instead. This expansion keeps the factory used, so a
/// table and the macro output agree on which factories exist.
#[cfg(not(feature = "inventory"))]
#[doc(hidden)]
#[macro_export]
macro_rules! __register_host_descriptor {
    ($factory:path $(,)?) => {
        const _: fn() -> $crate::HostDescriptor = $factory;
    };
}

/// Requests the framework `KItem`/`KResult` descriptors for one definition.
///
/// This is an expansion boundary; authors use it indirectly through
/// `sorts!` whenever a parent or membership line names a framework sort.
#[cfg(feature = "inventory")]
#[doc(hidden)]
#[macro_export]
macro_rules! __request_framework_sorts {
    () => {
        $crate::__private::inventory::submit! {
            $crate::__private::FrameworkSortRequest::new(env!("CARGO_MANIFEST_DIR"))
        }
    };
}

/// Accepts a framework-sort request without registering it.
///
/// Without the `inventory` feature, the request is recorded by the crate's
/// explicit registration table instead.
#[cfg(not(feature = "inventory"))]
#[doc(hidden)]
#[macro_export]
macro_rules! __request_framework_sorts {
    () => {
        const _: () = ();
    };
}

/// Implementation details used by generated registration expansions.
///
/// No item in this module is a stable author-facing API. It is public only
/// because a macro expanded in a downstream crate must be able to name it.
#[doc(hidden)]
pub mod __private {
    use super::HostDescriptor;

    #[cfg(feature = "inventory")]
    #[doc(hidden)]
    pub use inventory;

    /// One semantics crate's explicit registration table.
    ///
    /// A whole-crate step emits this as the crate-root
    /// `__KRS_REGISTRATIONS` static. `register` pushes every factory under
    /// the `#[cfg]` attributes of the item that defines it.
    #[doc(hidden)]
    pub struct RegistrationTable {
        /// `CARGO_MANIFEST_DIR` of the registering crate.
        pub manifest_dir: &'static str,
        /// Whether any `sorts!` in the crate names `KItem` or `KResult`.
        pub requests_framework: bool,
        /// Pushes each descriptor factory of the crate.
        pub register: fn(&mut Registrar),
    }

    /// Accumulates descriptor factories from explicit registration tables.
    #[doc(hidden)]
    #[derive(Default)]
    pub struct Registrar {
        factories: Vec<fn() -> HostDescriptor>,
    }

    impl Registrar {
        /// Records one descriptor factory.
        #[doc(hidden)]
        pub fn factory(&mut self, factory: fn() -> HostDescriptor) {
            self.factories.push(factory);
        }

        pub(crate) fn into_factories(self) -> Vec<fn() -> HostDescriptor> {
            self.factories
        }
    }

    /// One process-local registration entry.
    #[cfg(feature = "inventory")]
    #[doc(hidden)]
    pub struct HostRegistration {
        factory: fn() -> HostDescriptor,
        path: &'static str,
        manifest_dir: &'static str,
    }

    #[cfg(feature = "inventory")]
    impl HostRegistration {
        /// Creates an entry around a descriptor factory, its
        /// `module_path!()`-qualified path, and its crate's manifest
        /// directory.
        #[doc(hidden)]
        #[must_use]
        pub const fn new(
            factory: fn() -> HostDescriptor,
            path: &'static str,
            manifest_dir: &'static str,
        ) -> Self {
            Self {
                factory,
                path,
                manifest_dir,
            }
        }

        pub(crate) fn make(&self) -> HostDescriptor {
            (self.factory)()
        }
    }

    /// One downstream request for the framework sort descriptor pair.
    #[cfg(feature = "inventory")]
    #[doc(hidden)]
    pub struct FrameworkSortRequest {
        manifest_dir: &'static str,
    }

    #[cfg(feature = "inventory")]
    impl FrameworkSortRequest {
        /// Captures the requesting definition's manifest directory.
        #[doc(hidden)]
        #[must_use]
        pub const fn new(manifest_dir: &'static str) -> Self {
            Self { manifest_dir }
        }

        pub(crate) const fn manifest_dir(&self) -> &'static str {
            self.manifest_dir
        }
    }

    /// One linked factory as recorded by the inventory registration.
    #[cfg(feature = "inventory")]
    #[doc(hidden)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    pub struct CensusRegistration {
        /// `module_path!()`-qualified factory path.
        pub path: &'static str,
        /// `CARGO_MANIFEST_DIR` of the registering crate.
        pub manifest_dir: &'static str,
    }

    /// Every inventory registration linked into this process.
    ///
    /// This is test support for generating and checking explicit
    /// registration tables; it never enters a descriptor bundle.
    #[cfg(feature = "inventory")]
    #[doc(hidden)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub struct RegistrationCensus {
        /// Registered factories, sorted.
        pub registrations: Vec<CensusRegistration>,
        /// Manifest directories that requested the framework sorts, sorted
        /// and deduplicated.
        pub framework_requests: Vec<&'static str>,
    }

    /// Lists every linked registration and framework-sort request.
    #[cfg(feature = "inventory")]
    #[doc(hidden)]
    #[must_use]
    pub fn registration_census() -> RegistrationCensus {
        let mut registrations = inventory::iter::<HostRegistration>
            .into_iter()
            .map(|registration| CensusRegistration {
                path: registration.path,
                manifest_dir: registration.manifest_dir,
            })
            .collect::<Vec<_>>();
        registrations.sort_unstable();
        let mut framework_requests = inventory::iter::<FrameworkSortRequest>
            .into_iter()
            .map(FrameworkSortRequest::manifest_dir)
            .collect::<Vec<_>>();
        framework_requests.sort_unstable();
        framework_requests.dedup();
        RegistrationCensus {
            registrations,
            framework_requests,
        }
    }

    #[cfg(feature = "inventory")]
    inventory::collect!(HostRegistration);
    #[cfg(feature = "inventory")]
    inventory::collect!(FrameworkSortRequest);
}

#[cfg(test)]
mod tests {
    use std::any::TypeId;
    use std::collections::{BTreeMap, BTreeSet};
    use std::mem;

    use super::*;

    mod nested {
        use super::*;

        pub(super) fn descriptor() -> HostDescriptor {
            test_descriptor(module_path!(), "NestedSort")
        }

        crate::__register_host_descriptor!(descriptor);
    }

    trait ParentSort {}

    fn parent_sort_key() -> TypeId {
        TypeId::of::<dyn ParentSort>()
    }

    fn test_descriptor(rust_module_path: &str, item: &str) -> HostDescriptor {
        let position = |column| HostSourcePosition::new(1, column).expect("valid position");
        let anchor = HostSourceAnchor::new(
            "src/lib.rs",
            position(1),
            position(2),
            AnchorPrecision::Exact,
        )
        .expect("valid anchor");
        let provenance = HostProvenance::new(
            anchor.clone(),
            vec![HostAuthoredAnchor::new(
                ProvenanceKey::new("sort_item", 0).expect("valid role"),
                anchor,
            )],
        )
        .expect("valid provenance");

        HostDescriptor {
            protocol_version: ProtocolVersion::CURRENT,
            id: HostItemId::from_macro_context(
                env!("CARGO_PKG_NAME"),
                env!("CARGO_PKG_VERSION"),
                env!("CARGO_MANIFEST_DIR"),
                rust_module_path,
                item,
                ItemKind::Sort,
                "",
            )
            .expect("valid item"),
            declared_type: None,
            payload: HostDescriptorPayload::Sort(HostSortDescriptor {
                parents: vec![HostTypeReference {
                    key: HostTypeKey(parent_sort_key),
                    authored_path: "owned::ParentSort".to_owned(),
                }],
            }),
            cfg: BTreeMap::new(),
            provenance,
        }
    }

    #[test]
    fn term_is_only_a_zero_sized_sort_annotation() {
        trait OpenSort {}

        assert_eq!(mem::size_of::<Term<dyn OpenSort>>(), 0);
        assert_eq!(mem::size_of::<KItem>(), 0);
        assert_eq!(mem::size_of::<KResult>(), 0);
        assert_ne!(TypeId::of::<KItem>(), TypeId::of::<KResult>());
        assert_eq!(mem::size_of::<builtin::KSequence>(), 0);
        assert_eq!(mem::size_of::<builtin::Id>(), 0);
        assert_eq!(mem::size_of::<builtin::Map>(), 0);
        assert_eq!(mem::size_of::<builtin::List>(), 0);
        assert_eq!(mem::size_of::<configuration::Cell<builtin::Map>>(), 0);
        assert_eq!(
            mem::size_of::<configuration::KCell<builtin::KSequence>>(),
            0
        );
    }

    #[test]
    fn calc_configuration_value_shells_are_rust_checked_and_zero_sized() {
        use crate as language;
        use language::builtin::{Id, KSequence, Map};
        use language::configuration::{Cell, KCell};

        trait Value {}
        type Environment = Map<Id, Term<dyn Value>>;

        struct Machine {
            k: KCell<KSequence>,
            env: Cell<Environment>,
        }

        fn initialize(environment: Environment) -> Machine {
            Machine {
                k: KCell::new(KSequence::__new()),
                env: Cell::new(environment),
            }
        }

        let Machine { k, env } = initialize(Environment::__new());
        assert_eq!(mem::size_of_val(&k), 0);
        assert_eq!(mem::size_of_val(&env), 0);

        // The configuration parser deliberately erases the useful generic
        // arguments before asking the builtin registry to join the outer sort.
        let registry = language::builtin_registry();
        assert_eq!(
            registry.resolve_sort(TypeId::of::<Map>()),
            Some(BuiltinSort::Map)
        );
        assert_eq!(registry.resolve_sort(TypeId::of::<Environment>()), None);
    }

    #[test]
    fn protocol_v7_host_contracts_are_reexported_through_a_facade_alias() {
        use crate as language;

        let _: Option<language::HostFixedConfiguration> = None;
        let _: Option<language::HostConfigurationRule> = None;
        let _: Option<language::HostCellDeclaration> = None;
        let _: Option<language::HostInitializerCell> = None;
        let _: Option<language::HostRuleBinding> = None;
        let _: Option<language::HostRuleCells> = None;
        let _: Option<language::ProtocolRuleBinding<language::HostSortReference>> = None;
        let _: Option<language::ProtocolRuleBindingKind<language::HostSortReference>> = None;
        let _: Option<language::ProtocolRuleFrame> = None;
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Exhaustively verifies every facade registry identity.
    fn builtin_registry_is_complete_and_exact() {
        let registry = builtin_registry();
        registry.validate().expect("facade catalog is valid");
        registry
            .validate_v7()
            .expect("facade protocol-v7 catalog is valid");

        assert_eq!(registry.sorts.len(), BuiltinSort::ALL.len());
        assert_eq!(registry.operations.len(), BuiltinOperation::ALL.len());
        assert_eq!(
            registry.map_operations.len(),
            MapOperation::TERM_APPLICATIONS.len()
        );
        assert_eq!(
            registry.list_operations.len(),
            ListOperation::TERM_APPLICATIONS.len()
        );
        assert_eq!(
            registry
                .sorts
                .iter()
                .map(|registration| registration.sort)
                .collect::<BTreeSet<_>>(),
            BuiltinSort::ALL.into_iter().collect()
        );
        assert_eq!(
            registry
                .operations
                .iter()
                .map(|registration| registration.operation)
                .collect::<BTreeSet<_>>(),
            BuiltinOperation::ALL.into_iter().collect()
        );

        let exact_sorts = [
            (TypeId::of::<builtin::KSequence>(), BuiltinSort::KSequence),
            (TypeId::of::<builtin::int::Int>(), BuiltinSort::Int),
            (TypeId::of::<builtin::bool::Bool>(), BuiltinSort::Bool),
            (TypeId::of::<builtin::Map>(), BuiltinSort::Map),
            (TypeId::of::<builtin::Id>(), BuiltinSort::Id),
            (TypeId::of::<builtin::Bytes>(), BuiltinSort::Bytes),
            (TypeId::of::<builtin::List>(), BuiltinSort::List),
            (TypeId::of::<builtin::Set>(), BuiltinSort::Set),
        ];
        for (marker, expected) in exact_sorts {
            assert_eq!(registry.resolve_sort(marker), Some(expected));
            assert_eq!(registry.resolve_operation(marker), None);
        }

        let exact_operations = [
            (TypeId::of::<builtin::int::add>(), BuiltinOperation::IntAdd),
            (TypeId::of::<builtin::int::sub>(), BuiltinOperation::IntSub),
            (TypeId::of::<builtin::int::mul>(), BuiltinOperation::IntMul),
            (TypeId::of::<builtin::int::div>(), BuiltinOperation::IntTDiv),
            (
                TypeId::of::<builtin::int::modulo>(),
                BuiltinOperation::IntMod,
            ),
            (
                TypeId::of::<builtin::int::pow_mod>(),
                BuiltinOperation::IntPowMod,
            ),
            (
                TypeId::of::<builtin::int::log2>(),
                BuiltinOperation::IntLog2,
            ),
            (
                TypeId::of::<builtin::int::shift_right>(),
                BuiltinOperation::IntShiftRight,
            ),
            (
                TypeId::of::<builtin::int::shift_left>(),
                BuiltinOperation::IntShiftLeft,
            ),
            (
                TypeId::of::<builtin::int::bit_and>(),
                BuiltinOperation::IntBitAnd,
            ),
            (
                TypeId::of::<builtin::int::bit_xor>(),
                BuiltinOperation::IntBitXor,
            ),
            (
                TypeId::of::<builtin::int::bit_or>(),
                BuiltinOperation::IntBitOr,
            ),
            (
                TypeId::of::<builtin::int::ge>(),
                BuiltinOperation::IntGreaterEqual,
            ),
            (
                TypeId::of::<builtin::int::gt>(),
                BuiltinOperation::IntGreater,
            ),
            (
                TypeId::of::<builtin::int::le>(),
                BuiltinOperation::IntLessEqual,
            ),
            (TypeId::of::<builtin::int::lt>(), BuiltinOperation::IntLess),
            (TypeId::of::<builtin::int::eq>(), BuiltinOperation::IntEqual),
            (
                TypeId::of::<builtin::int::ne>(),
                BuiltinOperation::IntNotEqual,
            ),
            (
                TypeId::of::<builtin::bool::not>(),
                BuiltinOperation::BoolNot,
            ),
            (
                TypeId::of::<builtin::bool::eq>(),
                BuiltinOperation::BoolEqual,
            ),
            (
                TypeId::of::<builtin::bool::ne>(),
                BuiltinOperation::BoolNotEqual,
            ),
            (
                TypeId::of::<builtin::bool::and>(),
                BuiltinOperation::BoolAnd,
            ),
            (TypeId::of::<builtin::bool::or>(), BuiltinOperation::BoolOr),
            (
                TypeId::of::<builtin::bytes::length>(),
                BuiltinOperation::BytesLength,
            ),
            (
                TypeId::of::<builtin::bytes::get>(),
                BuiltinOperation::BytesGet,
            ),
            (
                TypeId::of::<builtin::bytes::empty>(),
                BuiltinOperation::BytesEmpty,
            ),
            (
                TypeId::of::<builtin::bytes::update>(),
                BuiltinOperation::BytesUpdate,
            ),
            (
                TypeId::of::<builtin::bytes::pad_right>(),
                BuiltinOperation::BytesPadRight,
            ),
            (
                TypeId::of::<builtin::bytes::substr>(),
                BuiltinOperation::BytesSubstring,
            ),
        ];
        for (marker, expected) in exact_operations {
            assert_eq!(registry.resolve_operation(marker), Some(expected));
            assert_eq!(registry.resolve_sort(marker), None);
        }
        for (marker, expected) in [
            (TypeId::of::<builtin::map::update>(), MapOperation::Update),
            (TypeId::of::<builtin::map::get>(), MapOperation::Get),
            (TypeId::of::<builtin::map::in_keys>(), MapOperation::InKeys),
        ] {
            assert_eq!(registry.resolve_map_operation(marker), Some(expected));
            assert_eq!(registry.resolve_operation(marker), None);
        }
        let exact_list_operations = [
            (TypeId::of::<builtin::list::empty>(), ListOperation::Empty),
            (TypeId::of::<builtin::list::item>(), ListOperation::Item),
            (TypeId::of::<builtin::list::concat>(), ListOperation::Concat),
            (TypeId::of::<builtin::list::get>(), ListOperation::Get),
            (TypeId::of::<builtin::list::update>(), ListOperation::Update),
            (TypeId::of::<builtin::list::size>(), ListOperation::Size),
            (TypeId::of::<builtin::list::make>(), ListOperation::Make),
            (TypeId::of::<builtin::list::range>(), ListOperation::Range),
            (
                TypeId::of::<builtin::list::update_all>(),
                ListOperation::UpdateAll,
            ),
        ];
        for (marker, expected) in exact_list_operations {
            assert_eq!(registry.resolve_list_operation(marker), Some(expected));
            assert_eq!(registry.resolve_sort(marker), None);
            assert_eq!(registry.resolve_operation(marker), None);
            assert_eq!(registry.resolve_map_operation(marker), None);
        }
        let exact_set_operations = [
            (TypeId::of::<builtin::set::empty>(), SetOperation::Empty),
            (TypeId::of::<builtin::set::item>(), SetOperation::Item),
            (TypeId::of::<builtin::set::concat>(), SetOperation::Concat),
            (
                TypeId::of::<builtin::set::contains>(),
                SetOperation::Contains,
            ),
        ];
        for (marker, expected) in exact_set_operations {
            assert_eq!(registry.resolve_set_operation(marker), Some(expected));
            assert_eq!(registry.resolve_sort(marker), None);
            assert_eq!(registry.resolve_operation(marker), None);
            assert_eq!(registry.resolve_map_operation(marker), None);
            assert_eq!(registry.resolve_list_operation(marker), None);
        }
    }

    #[test]
    fn same_signature_operations_have_distinct_marker_identities() {
        assert_ne!(
            TypeId::of::<builtin::int::add>(),
            TypeId::of::<builtin::int::sub>()
        );
        assert_ne!(
            TypeId::of::<builtin::int::eq>(),
            TypeId::of::<builtin::int::ne>()
        );
        assert_ne!(
            TypeId::of::<builtin::bool::eq>(),
            TypeId::of::<builtin::bool::ne>()
        );
        assert_ne!(
            TypeId::of::<builtin::bool::and>(),
            TypeId::of::<builtin::bool::or>()
        );
        let conjunction: builtin::bool::and =
            builtin::bool::and(builtin::bool::Bool, builtin::bool::Bool);
        let _: builtin::bool::And = conjunction;
    }

    #[test]
    fn module_import_and_facade_aliases_preserve_callable_identity() {
        use crate as dialect;
        use dialect::builtin::int as integer;
        use dialect::builtin::list::get as indexed_lookup;
        use dialect::builtin::map::update as persistent_update;
        use integer::add as plus;

        let application: plus = plus(integer::Int, integer::Int);
        let _: integer::add = application;
        assert_eq!(
            TypeId::of::<dialect::builtin::int::add>(),
            TypeId::of::<plus>()
        );
        assert_eq!(
            dialect::builtin_registry().resolve_operation(TypeId::of::<plus>()),
            Some(BuiltinOperation::IntAdd)
        );
        let updated: persistent_update =
            persistent_update(dialect::builtin::Map::__new(), dialect::builtin::Id, ());
        let _: dialect::builtin::map::Update = updated;
        assert_eq!(
            TypeId::of::<persistent_update>(),
            TypeId::of::<dialect::builtin::map::Update>()
        );
        assert_eq!(
            dialect::builtin_registry().resolve_map_operation(TypeId::of::<persistent_update>()),
            Some(MapOperation::Update)
        );
        let lookup: indexed_lookup = indexed_lookup(dialect::builtin::List::__new(), integer::Int);
        let _: dialect::builtin::list::Get = lookup;
        assert_eq!(
            dialect::builtin_registry().resolve_list_operation(TypeId::of::<indexed_lookup>()),
            Some(ListOperation::Get)
        );
    }

    fn register_nested(registrar: &mut __private::Registrar) {
        registrar.factory(nested::descriptor);
    }

    fn table(manifest_dir: &'static str, requests_framework: bool) -> __private::RegistrationTable {
        __private::RegistrationTable {
            manifest_dir,
            requests_framework,
            register: register_nested,
        }
    }

    #[cfg(feature = "inventory")]
    fn item_ids(descriptors: impl Iterator<Item = HostDescriptor>) -> Vec<HostItemId> {
        let mut ids = descriptors
            .map(|descriptor| descriptor.id)
            .collect::<Vec<_>>();
        ids.sort();
        ids
    }

    fn item_names(descriptors: impl Iterator<Item = HostDescriptor>) -> Vec<String> {
        let mut names = descriptors
            .map(|descriptor| descriptor.id.item_name().to_owned())
            .collect::<Vec<_>>();
        names.sort();
        names
    }

    #[test]
    fn explicit_tables_without_a_framework_request_omit_the_framework_pair() {
        let downstream = table("/definitions/downstream", false);
        assert_eq!(
            item_names(host_descriptors_from(&[&downstream])),
            ["NestedSort"]
        );
        assert!(host_descriptors_from(&[]).next().is_none());
    }

    #[test]
    fn explicit_downstream_framework_request_includes_the_framework_pair() {
        let downstream = table("/definitions/downstream", true);
        let unrequested = table("/definitions/other", false);
        assert_eq!(
            item_names(host_descriptors_from(&[&unrequested, &downstream])),
            ["KItem", "KResult", "NestedSort", "NestedSort"]
        );
        let framework = host_descriptors_from(&[&downstream])
            .filter(|descriptor| descriptor.id.item_name() != "NestedSort")
            .collect::<Vec<_>>();
        assert_eq!(framework.len(), FRAMEWORK_FACTORIES.len());
        for descriptor in &framework {
            assert_eq!(descriptor.id.item_kind(), ItemKind::Sort);
            assert_eq!(descriptor.id.rust_module_path(), [env!("CARGO_CRATE_NAME")]);
            assert_eq!(
                descriptor.id.package().manifest_dir(),
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            );
        }
    }

    #[test]
    fn explicit_framework_request_from_krs_itself_is_ignored() {
        let facade = table(env!("CARGO_MANIFEST_DIR"), true);
        assert_eq!(
            item_names(host_descriptors_from(&[&facade])),
            ["NestedSort"]
        );
    }

    #[cfg(feature = "inventory")]
    #[test]
    fn framework_factory_table_matches_inventory_framework_registrations() {
        let from_inventory = item_ids(
            inventory::iter::<__private::HostRegistration>
                .into_iter()
                .map(__private::HostRegistration::make)
                .filter(is_framework_sort_descriptor),
        );
        let from_table = item_ids(FRAMEWORK_FACTORIES.iter().map(|factory| factory()));
        assert_eq!(from_inventory.len(), 2);
        assert_eq!(from_table, from_inventory);
    }

    #[cfg(feature = "inventory")]
    #[test]
    fn census_table_matches_inventory_enumeration() {
        let census = __private::registration_census();
        let own = census
            .registrations
            .iter()
            .filter(|registration| registration.manifest_dir == env!("CARGO_MANIFEST_DIR"))
            .map(|registration| registration.path)
            .filter(|path| !path.starts_with("krs::__krs_sort_descriptor_"))
            .collect::<Vec<_>>();
        assert_eq!(own, ["krs::tests::nested::descriptor"]);
        assert_eq!(census.framework_requests, [env!("CARGO_MANIFEST_DIR")]);

        let requests_framework = census
            .framework_requests
            .contains(&env!("CARGO_MANIFEST_DIR"));
        let explicit = table(env!("CARGO_MANIFEST_DIR"), requests_framework);
        assert_eq!(
            item_ids(host_descriptors_from(&[&explicit])),
            item_ids(host_descriptors())
        );
    }

    #[cfg(feature = "inventory")]
    #[test]
    fn enumeration_invokes_factories_for_fresh_owned_values() {
        let mut first = host_descriptors()
            .find(|descriptor| descriptor.id.item_name() == "NestedSort")
            .expect("nested registration is linked");
        first
            .cfg
            .insert("mutated".to_owned(), Some("locally".to_owned()));
        let HostDescriptorPayload::Sort(sort) = &mut first.payload else {
            panic!("test registration is a sort")
        };
        sort.parents.clear();

        let second = host_descriptors()
            .find(|descriptor| descriptor.id.item_name() == "NestedSort")
            .expect("nested registration remains linked");
        assert!(!second.cfg.contains_key("mutated"));
        assert_eq!(second.id.package().cargo_name(), env!("CARGO_PKG_NAME"));
        assert_eq!(
            second.id.rust_module_path(),
            &["krs".to_owned(), "tests".to_owned(), "nested".to_owned()]
        );
        let HostDescriptorPayload::Sort(sort) = second.payload else {
            panic!("test registration is a sort")
        };
        assert_eq!(sort.parents.len(), 1);
        assert_eq!(sort.parents[0].authored_path, "owned::ParentSort");
    }
}
