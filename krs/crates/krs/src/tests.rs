//! Unit tests of the facade's registration, wire decoding and provenance
//! helpers, kept apart from `lib.rs` so that a fixture edit leaves the
//! facade's own source, which every framework origin names by content
//! hash, unchanged.

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
            parents: vec![krs_ir::HostSortReference {
                key: krs_ir::ProvenanceRole::SortParent.key(0),
                target: HostTypeReference {
                    key: HostTypeKey(parent_sort_key),
                    authored_path: "owned::ParentSort".to_owned(),
                },
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

fn table() -> __private::RegistrationTable {
    __private::RegistrationTable {
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
fn explicit_tables_always_include_the_framework_pair() {
    assert_eq!(item_names(host_descriptors_from(&[])), ["KItem", "KResult"]);
    let downstream = table();
    assert_eq!(
        item_names(host_descriptors_from(&[&downstream, &downstream])),
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
fn inventory_enumeration_includes_the_framework_pair() {
    assert_eq!(
        item_names(host_descriptors()),
        ["KItem", "KResult", "NestedSort"]
    );
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

    let explicit = table();
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
    assert_eq!(sort.parents[0].target.authored_path, "owned::ParentSort");
}
