//! Author-facing Rust host types and registration for KRS definitions.
//!
//! Procedural macros eventually generate ordinary Rust declarations plus a
//! small host-descriptor factory. The factory is registered through
//! [`__register_host_descriptor!`], and a generated host collector obtains
//! freshly owned descriptors from [`host_descriptors`]. Registration order is
//! deliberately unspecified and has no semantic meaning.
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
    ConfigurationDescriptorError, HostAuthoredAnchor, HostBuiltinOperationRegistration,
    HostBuiltinRegistry, HostBuiltinRegistryError, HostBuiltinSortRegistration,
    HostConfigurationDescriptor, HostConfigurationInitializerDescriptor,
    HostConfigurationVariableDescriptor, HostConstructorDescriptor, HostConstructorFieldDescriptor,
    HostDeclarationIdentity, HostDescriptor, HostDescriptorPayload, HostDescriptorReference,
    HostIdentityError, HostItemId, HostMapOperationRegistration, HostPackageKey, HostProvenance,
    HostProvenanceError, HostRuleDescriptor, HostRuleParameterDescriptor, HostSortDescriptor,
    HostSourceAnchor, HostSourcePosition, HostTypeKey, HostTypeReference, ItemKind, MapOperation,
    ProtocolVersion, ProvenanceKey, RuleBindingError, SentenceKind,
};
pub use krs_ir::{
    DescriptorApplicationHeadClass, DescriptorAssociativitySentence, DescriptorFieldReference,
    DescriptorFormatFragment, DescriptorGroupReference, DescriptorLexicalPrecedence,
    DescriptorLiteral, DescriptorPrecedenceChain, DescriptorRuleCondition, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSimplification, DescriptorSimplificationPriority,
    FormatFragment, GroupAssociativity, HostApplicationIdentity, HostApplicationReference,
    HostApplicationTarget, HostContextAliasReference, HostEnumVariantKey, HostEnumVariantReference,
    HostEnumVariantReferenceError, HostGrammarDescriptor, HostProduction, HostProductionAttribute,
    HostProductionItem, HostProductionOwner, HostRuleCondition, HostSortReference,
    HostStructuredRuleDescriptor, HostTerm, HostTermArgument, ProductionFieldId, ProductionGroupId,
    ProtocolV6ShapeError, StrictnessKind, enum_variant_disambiguator,
};
// These protocol-v7 host contracts are reexported because downstream proc
// macro expansions must name them through the actual (possibly renamed) KRS
// facade dependency. Stable descriptor counterparts remain in `krs-ir`.
pub use krs_ir::protocol_v7::{
    CellWrapper, ClaimModality, DescriptorCellColor, DescriptorCellName,
    DescriptorConfigurationRoot, DescriptorKSequenceNotation, HostCellDeclaration,
    HostCellDeclarationReference, HostCellField, HostCellIdentity, HostCellReference, HostClaim,
    HostClaimBinder, HostConfigurationDeclaration, HostConfigurationInitializer,
    HostConfigurationReference, HostConfigurationRule, HostConfigurationVariable, HostContextAlias,
    HostFixedConfiguration, HostInitializerCell, HostInitializerStateTerm, HostRuleBinding,
    HostRuleCells, ProtocolCellContent, ProtocolCellDeclaration, ProtocolCellField,
    ProtocolConfigurationInitializer, ProtocolConfigurationVariable, ProtocolContextAliasBinding,
    ProtocolContextAliasBindingKind, ProtocolInitializerCell, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolInitializerTerm, ProtocolKSequence,
    ProtocolKSequenceItem, ProtocolMap, ProtocolMapBody, ProtocolMapItem, ProtocolRuleBinding,
    ProtocolRuleBindingKind, ProtocolRuleCell, ProtocolRuleCells, ProtocolRuleFrame,
    ProtocolRuleKSequence, ProtocolRuleKSequenceItem, ProtocolRuleMap, ProtocolRuleMapBody,
    ProtocolRuleMapItem, ProtocolRuleStateTerm, ProtocolV7ShapeError,
};
pub use krs_ir::{
    DescriptorHeadRule, DescriptorHeadRuleBinding, DescriptorHeadRuleExtra,
    DescriptorHeadRuleResult, HostHeadRule, HostHeadRuleBinding, HostHeadRuleCellReference,
    HostHeadRuleExtra, HostHeadRuleResult, ProtocolHeadRuleBinding, ProtocolHeadRuleExtra,
    ProtocolHeadRuleResult,
};
pub use krs_macros::{
    alias, anonymous, associativity, bracket, bytes, cell, cells, claim, configuration,
    constructor, constructors, context_alias, ensures, equation, exists, function, id, init, k,
    map, or_bool, precedence, priority, requires, rule, rules, seqstrict, simplification, sort,
    sorts, strict, subsort, symbol, term, token,
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
// definition whose sort graph names either one.
krs_macros::sorts! {
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
        pub use Div as div;
        pub use Ge as ge;
        pub use Gt as gt;
        pub use Le as le;
        pub use Lt as lt;
        pub use Mul as mul;
        pub use Ne as ne;
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

        pub use Get as get;
        pub use Length as length;
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
}

fn map_update_builtin_key() -> TypeId {
    TypeId::of::<builtin::map::update>()
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
    ]
    .into_iter()
    .map(|(operation, key)| HostBuiltinOperationRegistration {
        operation,
        target: HostTypeKey(key),
    })
    .collect();

    let map_operations = vec![HostMapOperationRegistration {
        operation: MapOperation::Update,
        target: HostTypeKey(map_update_builtin_key),
    }];

    HostBuiltinRegistry {
        sorts,
        operations,
        map_operations,
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
#[doc(hidden)]
#[macro_export]
macro_rules! __register_host_descriptor {
    ($factory:path $(,)?) => {
        $crate::__private::inventory::submit! {
            $crate::__private::HostRegistration::new($factory)
        }
    };
}

/// Requests the framework `KItem`/`KResult` descriptors for one definition.
///
/// This is an expansion boundary; authors use it indirectly through
/// `sorts!` whenever a parent or membership line names a framework sort.
#[doc(hidden)]
#[macro_export]
macro_rules! __request_framework_sorts {
    () => {
        $crate::__private::inventory::submit! {
            $crate::__private::FrameworkSortRequest::new(env!("CARGO_MANIFEST_DIR"))
        }
    };
}

/// Implementation details used by generated registration expansions.
///
/// No item in this module is a stable author-facing API. It is public only
/// because a macro expanded in a downstream crate must be able to name it.
#[doc(hidden)]
pub mod __private {
    use super::HostDescriptor;

    #[doc(hidden)]
    pub use inventory;

    /// One process-local registration entry.
    #[doc(hidden)]
    pub struct HostRegistration {
        factory: fn() -> HostDescriptor,
    }

    impl HostRegistration {
        /// Creates an entry around a descriptor factory.
        #[doc(hidden)]
        #[must_use]
        pub const fn new(factory: fn() -> HostDescriptor) -> Self {
            Self { factory }
        }

        pub(crate) fn make(&self) -> HostDescriptor {
            (self.factory)()
        }
    }

    /// One downstream request for the framework sort descriptor pair.
    #[doc(hidden)]
    pub struct FrameworkSortRequest {
        manifest_dir: &'static str,
    }

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

    inventory::collect!(HostRegistration);
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

        fn descriptor() -> HostDescriptor {
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
        ];
        for (marker, expected) in exact_operations {
            assert_eq!(registry.resolve_operation(marker), Some(expected));
            assert_eq!(registry.resolve_sort(marker), None);
        }
        assert_eq!(
            registry.resolve_map_operation(TypeId::of::<builtin::map::update>()),
            Some(MapOperation::Update)
        );
        assert_eq!(
            registry.resolve_operation(TypeId::of::<builtin::map::update>()),
            None
        );
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
    }

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
