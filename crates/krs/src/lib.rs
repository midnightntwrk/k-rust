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

mod provenance;

#[doc(hidden)]
pub use provenance::{__KrsRawAnchor, __KrsRawProvenance, __krs_host_provenance};

pub use krs_ir::{
    AnchorPrecision, BuiltinOperation, BuiltinSort, HookOperation, HostAuthoredAnchor,
    HostBuiltinRegistry, HostBuiltinRegistryError, HostConstructorDescriptor,
    HostConstructorFieldDescriptor, HostDeclarationIdentity, HostDescriptor, HostDescriptorPayload,
    HostIdentityError, HostItemId, HostPackageKey, HostProvenance, HostProvenanceError,
    HostProvenanceShapeError, HostSortDescriptor, HostSourceAnchor, HostSourcePosition,
    HostTypeKey, HostTypeReference, ItemKind, ListOperation, MapOperation, ProvenanceKey,
    ProvenanceRole, SchemaVersion, SentenceKind, SetOperation, TermMapOperation,
};
pub use krs_ir::{
    DescriptorApplicationHeadClass, DescriptorAssociativitySentence, DescriptorFieldReference,
    DescriptorFormatFragment, DescriptorGroupReference, DescriptorLexicalPrecedence,
    DescriptorLiteral, DescriptorPrecedenceChain, DescriptorRuleCondition, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSimplification, DescriptorSimplificationPriority,
    FormatFragment, GrammarTransportError, GroupAssociativity, HostApplicationIdentity,
    HostApplicationReference, HostApplicationTarget, HostCellTermField, HostContextAliasReference,
    HostEnumVariantKey, HostEnumVariantReference, HostEnumVariantReferenceError,
    HostGrammarDescriptor, HostProduction, HostProductionAttribute, HostProductionItem,
    HostProductionOwner, HostRuleCondition, HostSortReference, HostStructuredRuleDescriptor,
    HostTerm, HostTermArgument, ProductionFieldId, ProductionGroupId, StrictnessKind,
    enum_variant_disambiguator,
};
// These configuration host contracts are reexported because downstream proc
// macro expansions must name them through the actual (possibly renamed) KRS
// facade dependency. Stable descriptor counterparts remain in `krs-ir`.
pub use krs_ir::{
    CellWrapper, ClaimModality, DescriptorCellColor, DescriptorCellExit,
    DescriptorCellMultiplicity, DescriptorCellName, DescriptorCellStream, DescriptorCellType,
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
    ProtocolRuleMapItem, ProtocolRuleStateTerm, StateTransportError,
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
    init, k, layout, lexeme, lexical, map, or_bool, precedence, priority, raw_k, requires, rule,
    rules, seqstrict, simplification, sort, sorts, strict, subsort, symbol, syntax_list, term,
    token,
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
// definition whose sort graph names either one. The invocation lists their
// factories only in `FRAMEWORK_FACTORIES`, which both entry points run when a
// definition requests them. Collection reparses this file and resolves this
// block through the crate facade name.
use krs_macros::__framework_sorts;
crate::__framework_sorts! {
    KItem;
    KResult: KItem;
}

pub mod builtin;

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
impl KItemSort for builtin::String {}
impl KResultSort for builtin::String {}
impl KItemSort for builtin::Float {}
impl KResultSort for builtin::Float {}

macro_rules! builtin_sort_registry {
    ($(
        $(#[$meta:meta])*
        $variant:ident {
            marker_name: $marker:ident,
            $($fact:tt)*
        }
    )*) => {
        fn builtin_sort_registry() -> [HostTypeKey; BuiltinSort::ALL.len()] {
            [$(HostTypeKey(TypeId::of::<builtin::$marker>)),*]
        }
    };
}

krs_ir::__krs_builtin_sort_catalog!(builtin_sort_registry);

macro_rules! builtin_operation_registry {
    ($(
        $(#[$meta:meta])*
        $variant:ident {
            rust_module: $module:ident,
            rust_name: $name:ident,
            $($fact:tt)*
        }
    )*) => {
        fn builtin_operation_registry() -> [HostTypeKey; BuiltinOperation::ALL.len()] {
            [$(HostTypeKey(TypeId::of::<builtin::$module::$name>)),*]
        }
    };
}

krs_ir::__krs_builtin_operation_catalog!(builtin_operation_registry);

macro_rules! map_operation_registry {
    (
        rust_module: $module:ident;
        structural { $($structural:tt)* }
        term {
            $(
                $(#[$meta:meta])*
                $variant:ident {
                    rust_name: $name:ident,
                    $($fact:tt)*
                }
            )*
        }
    ) => {
        fn map_operation_registry() -> [HostTypeKey; TermMapOperation::ALL.len()] {
            [$(HostTypeKey(TypeId::of::<builtin::$module::$name>)),*]
        }
    };
}

krs_ir::__krs_map_operation_catalog!(map_operation_registry);

macro_rules! list_operation_registry {
    (
        rust_module: $module:ident;
        $(
            $(#[$meta:meta])*
            $variant:ident {
                rust_name: $name:ident,
                $($fact:tt)*
            }
        )*
    ) => {
        fn list_operation_registry() -> [HostTypeKey; ListOperation::ALL.len()] {
            [$(HostTypeKey(TypeId::of::<builtin::$module::$name>)),*]
        }
    };
}

krs_ir::__krs_list_operation_catalog!(list_operation_registry);

macro_rules! set_operation_registry {
    (
        rust_module: $module:ident;
        $(
            $(#[$meta:meta])*
            $variant:ident {
                rust_name: $name:ident,
                $($fact:tt)*
            }
        )*
    ) => {
        fn set_operation_registry() -> [HostTypeKey; SetOperation::ALL.len()] {
            [$(HostTypeKey(TypeId::of::<builtin::$module::$name>)),*]
        }
    };
}

krs_ir::__krs_set_operation_catalog!(set_operation_registry);

/// Constructs the complete process-local registry of builtin Rust markers.
///
/// The registry joins rustc-resolved [`TypeId`] values to closed semantic
/// identities. It is intentionally host-only: aliases resolve because they
/// retain `TypeId`, while neither authored path spellings nor build-local keys
/// cross the compiler protocol boundary.
///
/// The returned registry has one entry for every [`BuiltinSort::ALL`],
/// [`BuiltinOperation::ALL`], [`TermMapOperation::ALL`], [`ListOperation::ALL`],
/// and [`SetOperation::ALL`] member and passes [`HostBuiltinRegistry::validate`].
#[must_use]
pub fn builtin_registry() -> HostBuiltinRegistry {
    HostBuiltinRegistry {
        sorts: builtin_sort_registry(),
        operations: builtin_operation_registry(),
        map_operations: map_operation_registry(),
        list_operations: list_operation_registry(),
        set_operations: set_operation_registry(),
    }
}

pub mod configuration;

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

/// Returns all host descriptor factory results linked into this collector process.
///
/// The framework `KItem`/`KResult` descriptor results are included when some linked definition requests them, matching [`host_descriptors_from`].
/// Each registered function constructs a fresh descriptor or returns a provenance error.
/// Owned strings and vectors are legal descriptor data.
/// The iterator follows the registration mechanism's unspecified enumeration order.
/// Collectors must deterministically select factory errors and order descriptors by stable identity before producing compiler input.
///
/// This entry point requires the default `inventory` feature.
/// Collectors built without it enumerate generated tables through [`host_descriptors_from`].
#[cfg(feature = "inventory")]
pub fn host_descriptors() -> impl Iterator<Item = Result<HostDescriptor, HostProvenanceError>> {
    let framework_requested = inventory::iter::<__private::FrameworkSortRequest>
        .into_iter()
        .next()
        .is_some();
    let framework: &[fn() -> Result<HostDescriptor, HostProvenanceError>] = if framework_requested {
        FRAMEWORK_FACTORIES
    } else {
        &[]
    };
    framework
        .iter()
        .map(|factory| factory())
        .chain(
            inventory::iter::<__private::HostRegistration>
                .into_iter()
                .map(__private::HostRegistration::make),
        )
        .collect::<Vec<_>>()
        .into_iter()
}

/// Returns the host descriptor factory results listed by explicit registration tables.
///
/// Each table belongs to one semantics crate and is written by a whole-crate step, because a procedural macro invocation cannot enumerate its sibling invocations.
/// The framework `KItem`/`KResult` descriptor results are included when some table requests them, matching [`host_descriptors`].
/// Collectors must deterministically select factory errors and order descriptors by stable identity.
///
/// This entry point needs no linker-section support and is available whether or not the `inventory` feature is enabled.
pub fn host_descriptors_from(
    tables: &[&__private::RegistrationTable],
) -> impl Iterator<Item = Result<HostDescriptor, HostProvenanceError>> {
    let framework_requested = tables.iter().any(|table| table.requests_framework);
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
        const _: fn()
            -> ::core::result::Result<$crate::HostDescriptor, $crate::HostProvenanceError> =
            $factory;
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

#[doc(hidden)]
#[path = "private.rs"]
pub mod __private;

#[cfg(test)]
mod tests {
    use std::any::TypeId;
    use std::collections::BTreeMap;
    use std::mem;

    use super::*;

    mod nested {
        use super::*;

        #[expect(
            clippy::unnecessary_wraps,
            reason = "Host-descriptor registration requires the fallible factory signature."
        )]
        pub(super) fn descriptor() -> Result<HostDescriptor, HostProvenanceError> {
            Ok(test_descriptor(module_path!(), "NestedSort"))
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
                ProvenanceKey::new(ProvenanceRole::SortDeclaration, 0),
                anchor,
            )],
        )
        .expect("valid provenance");

        HostDescriptor {
            protocol_version: SchemaVersion::CURRENT,
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
    fn configuration_host_contracts_are_reexported_through_a_facade_alias() {
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
        type IntAlias = builtin::int::Int;
        type MapAlias = builtin::Map;
        type BytesAlias = builtin::bytes::Bytes;
        type AddAlias = builtin::int::add;
        type NotAlias = builtin::bool::not;
        type SubstringAlias = builtin::bytes::substr;

        let registry = builtin_registry();
        registry.validate().expect("facade catalog is valid");
        for (marker, expected) in [
            (TypeId::of::<IntAlias>(), BuiltinSort::Int),
            (TypeId::of::<MapAlias>(), BuiltinSort::Map),
            (TypeId::of::<BytesAlias>(), BuiltinSort::Bytes),
        ] {
            assert_eq!(registry.resolve_sort(marker), Some(expected));
            assert_eq!(registry.resolve_operation(marker), None);
        }

        let operation_aliases = [
            (TypeId::of::<AddAlias>(), BuiltinOperation::IntAdd),
            (TypeId::of::<NotAlias>(), BuiltinOperation::BoolNot),
            (
                TypeId::of::<SubstringAlias>(),
                BuiltinOperation::BytesSubstring,
            ),
        ];
        for (marker, expected) in operation_aliases {
            assert_eq!(registry.resolve_operation(marker), Some(expected));
            assert_eq!(registry.resolve_sort(marker), None);
        }
        for (marker, expected) in [
            (
                TypeId::of::<builtin::map::update>(),
                TermMapOperation::Update,
            ),
            (TypeId::of::<builtin::map::get>(), TermMapOperation::Get),
            (
                TypeId::of::<builtin::map::in_keys>(),
                TermMapOperation::InKeys,
            ),
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
            (TypeId::of::<builtin::set::union>(), SetOperation::Union),
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
            Some(TermMapOperation::Update)
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

    fn table(requests_framework: bool) -> __private::RegistrationTable {
        __private::RegistrationTable {
            requests_framework,
            register: register_nested,
        }
    }

    #[cfg(feature = "inventory")]
    fn item_ids(
        descriptors: impl Iterator<Item = Result<HostDescriptor, HostProvenanceError>>,
    ) -> Vec<HostItemId> {
        let mut ids = descriptors
            .map(|descriptor| descriptor.unwrap().id)
            .collect::<Vec<_>>();
        ids.sort();
        ids
    }

    fn item_names(
        descriptors: impl Iterator<Item = Result<HostDescriptor, HostProvenanceError>>,
    ) -> Vec<String> {
        let mut names = descriptors
            .map(|descriptor| descriptor.unwrap().id.item_name().to_owned())
            .collect::<Vec<_>>();
        names.sort();
        names
    }

    #[test]
    fn explicit_tables_without_a_framework_request_omit_the_framework_pair() {
        let downstream = table(false);
        assert_eq!(
            item_names(host_descriptors_from(&[&downstream])),
            ["NestedSort"]
        );
        assert!(host_descriptors_from(&[]).next().is_none());
    }

    #[test]
    fn explicit_downstream_framework_request_includes_the_framework_pair() {
        let downstream = table(true);
        let unrequested = table(false);
        assert_eq!(
            item_names(host_descriptors_from(&[&unrequested, &downstream])),
            ["KItem", "KResult", "NestedSort", "NestedSort"]
        );
        let framework = host_descriptors_from(&[&downstream])
            .map(Result::unwrap)
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

    #[cfg(feature = "inventory")]
    #[test]
    fn framework_factories_are_listed_only_by_the_table() {
        let from_table = item_ids(FRAMEWORK_FACTORIES.iter().map(|factory| factory()));
        assert_eq!(from_table.len(), 2);
        let from_inventory = item_ids(
            inventory::iter::<__private::HostRegistration>
                .into_iter()
                .map(__private::HostRegistration::make),
        );
        assert!(from_table.iter().all(|id| !from_inventory.contains(id)));
    }

    #[cfg(feature = "inventory")]
    #[test]
    fn unrequested_framework_factories_are_not_run() {
        assert!(
            __private::registration_census()
                .framework_requests
                .is_empty()
        );
        assert_eq!(item_names(host_descriptors()), ["NestedSort"]);
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
            .collect::<Vec<_>>();
        assert_eq!(own, ["krs::tests::nested::descriptor"]);

        let explicit = table(!census.framework_requests.is_empty());
        assert_eq!(
            item_ids(host_descriptors_from(&[&explicit])),
            item_ids(host_descriptors())
        );
    }

    #[cfg(feature = "inventory")]
    #[test]
    fn enumeration_invokes_factories_for_fresh_owned_values() {
        let mut first = host_descriptors()
            .map(Result::unwrap)
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
            .map(Result::unwrap)
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

mod wire;

#[doc(hidden)]
pub use wire::{__KrsSlots, __KrsTargetSlot, __krs_host_payload};
