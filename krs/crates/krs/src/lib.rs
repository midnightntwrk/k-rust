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

mod bridge;
mod provenance;

// Every hidden seam of `bridge` is reexported, so adding one leaves this
// file, and the framework declarations' origins below, unchanged.
#[doc(hidden)]
pub use bridge::*;
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
    alias, anonymous, associativity, bracket, bytes, cell, cells, claim, claims, configuration,
    constant, constructor, constructors, context, context_alias, desugar, ensures, equation,
    equations, exists, fragment, fresh, function, id, init, is, k, layout, lexeme, lexical, map,
    matches, or_bool, precedence, priority, project, raw_k, requires, rewrite, rule, rules,
    seqstrict, simplification, sort, sorts, spec_module, strict, subsort, symbol, syntax_list,
    term, token,
};

// Framework identities are ordinary readable sorts that every definition
// has: `KItem` is the sort of computation items and `KResult` of evaluated
// results. The invocation lists their factories only in
// `FRAMEWORK_FACTORIES`, which both entry points always run; lowering emits
// their K module only where a declaration imports it. Collection reparses
// this file and resolves this block through the crate facade name.
use krs_macros::__framework_sorts;
crate::__framework_sorts! {
    KItem;
    KResult: KItem;
}

pub mod builtin;
pub mod ml;

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

/// Lets a one-segment path that names a builtin operation, such as
/// `set(m, k, v)` under `use k::builtin::map::update as set;`, resolve
/// through the same rustc witness as a constructor in a readable block or a
/// table: the witness's `set { .. }` pattern infers the operation's marker,
/// whose one impl fixes its defaulted parameters, and the target is the
/// marker's registry identity.
macro_rules! builtin_rule_applications {
    ($($module:ident::$name:ident),* $(,)?) => {
        $(
            impl<const SELECTOR: u64> __KrsRuleApplication<SELECTOR> for builtin::$module::$name {
                fn __krs_rule_application(authored_path: &str) -> HostApplicationTarget {
                    HostApplicationTarget::Nominal(HostTypeReference {
                        key: HostTypeKey(TypeId::of::<builtin::$module::$name>),
                        authored_path: authored_path.to_owned(),
                    })
                }
            }
        )*
    };
}

macro_rules! builtin_operation_registry {
    ($(
        $(#[$meta:meta])*
        $variant:ident {
            rust_module: $module:ident,
            rust_name: $name:ident,
            $($fact:tt)*
        }
    )*) => {
        builtin_rule_applications!($($module::$name),*);
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
        builtin_rule_applications!($($module::$name),*);
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
        builtin_rule_applications!($($module::$name),*);
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
        builtin_rule_applications!($($module::$name),*);
        fn set_operation_registry() -> [HostTypeKey; SetOperation::ALL.len()] {
            [$(HostTypeKey(TypeId::of::<builtin::$module::$name>)),*]
        }
    };
}

krs_ir::__krs_set_operation_catalog!(set_operation_registry);

macro_rules! ml_connective_registry {
    (
        rust_module: $module:ident;
        $(
            $(#[$meta:meta])*
            $variant:ident { rust_name: $name:ident, $($fact:tt)* }
        )*
    ) => {
        fn ml_connective_registry() -> [HostTypeKey; krs_ir::MlConnective::ALL.len()] {
            [$(HostTypeKey(TypeId::of::<$module::$name>)),*]
        }
    };
}

krs_ir::__krs_ml_connective_catalog!(ml_connective_registry);

macro_rules! operator_registry {
    ($(
        $(#[$meta:meta])*
        $variant:ident { rust_name: $name:ident, $($fact:tt)* }
    )*) => {
        fn operator_registry() -> [HostTypeKey; krs_ir::BuiltinOperator::ALL.len()] {
            [$(HostTypeKey(TypeId::of::<builtin::__operator::$name>)),*]
        }
    };
}

krs_ir::__krs_builtin_operator_catalog!(operator_registry);

fn list_notation_registry() -> [HostTypeKey; krs_ir::ListNotation::ALL.len()] {
    [
        HostTypeKey(TypeId::of::<builtin::__list::Cons>),
        HostTypeKey(TypeId::of::<builtin::__list::Empty>),
        HostTypeKey(TypeId::of::<builtin::__list::Snoc>),
    ]
}

/// Constructs the complete process-local registry of builtin Rust markers.
///
/// The registry joins rustc-resolved [`TypeId`] values to closed semantic
/// identities. It is intentionally host-only: aliases resolve because they
/// retain `TypeId`, while neither authored path spellings nor build-local keys
/// cross the compiler protocol boundary.
///
/// The returned registry has one entry for every [`BuiltinSort::ALL`],
/// [`BuiltinOperation::ALL`], [`TermMapOperation::ALL`], [`ListOperation::ALL`],
/// [`SetOperation::ALL`], [`krs_ir::MlConnective::ALL`],
/// [`krs_ir::BuiltinOperator::ALL`], and [`krs_ir::ListNotation::ALL`] member and passes
/// [`HostBuiltinRegistry::validate`].
#[must_use]
pub fn builtin_registry() -> HostBuiltinRegistry {
    HostBuiltinRegistry {
        sorts: builtin_sort_registry(),
        operations: builtin_operation_registry(),
        map_operations: map_operation_registry(),
        list_operations: list_operation_registry(),
        set_operations: set_operation_registry(),
        ml_connectives: ml_connective_registry(),
        operators: operator_registry(),
        list_notation: list_notation_registry(),
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
/// The framework `KItem`/`KResult` descriptor results are always included, matching [`host_descriptors_from`].
/// Each registered function constructs a fresh descriptor or returns a provenance error.
/// Owned strings and vectors are legal descriptor data.
/// The iterator follows the registration mechanism's unspecified enumeration order.
/// Collectors must deterministically select factory errors and order descriptors by stable identity before producing compiler input.
///
/// This entry point requires the default `inventory` feature.
/// Collectors built without it enumerate generated tables through [`host_descriptors_from`].
#[cfg(feature = "inventory")]
pub fn host_descriptors() -> impl Iterator<Item = Result<HostDescriptor, HostProvenanceError>> {
    FRAMEWORK_FACTORIES
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
/// The framework `KItem`/`KResult` descriptor results are always included, matching [`host_descriptors`].
/// Collectors must deterministically select factory errors and order descriptors by stable identity.
///
/// This entry point needs no linker-section support and is available whether or not the `inventory` feature is enabled.
pub fn host_descriptors_from(
    tables: &[&__private::RegistrationTable],
) -> impl Iterator<Item = Result<HostDescriptor, HostProvenanceError>> {
    let mut registrar = __private::Registrar::default();
    for factory in FRAMEWORK_FACTORIES {
        registrar.factory(*factory);
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

#[doc(hidden)]
#[path = "private.rs"]
pub mod __private;

#[cfg(test)]
mod tests;

mod wire;

#[doc(hidden)]
pub use wire::{__KrsSlots, __KrsTargetSlot, __krs_host_payload};
