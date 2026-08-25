//! Dependency-crate registration used by the host-collection fixture.

use std::collections::BTreeMap;

use k::{
    AnchorPrecision, HostAuthoredAnchor, HostDescriptor, HostDescriptorPayload, HostProvenance,
    HostItemId, HostSortDescriptor, HostSourceAnchor, HostSourcePosition, ItemKind, ProtocolVersion,
    ProvenanceKey,
};

/// An ordinary public symbol which a generated collector explicitly calls.
///
/// This intentional reference retains this semantics crate and its host
/// registrations in the final collector binary.
#[inline(never)]
pub fn retain_for_krs_collector() {
    std::hint::black_box(dependency_descriptor as fn() -> HostDescriptor);
}

fn dependency_descriptor() -> HostDescriptor {
    descriptor(module_path!(), "DependencySort")
}

k::__register_host_descriptor!(dependency_descriptor);

fn descriptor(rust_module_path: &str, item: &str) -> HostDescriptor {
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
        payload: HostDescriptorPayload::Sort(HostSortDescriptor::default()),
        cfg: BTreeMap::new(),
        provenance,
    }
}

#[cfg(test)]
mod tests {
    use std::any::TypeId;

    use k::BuiltinOperation;
    use k::builtin::int as integer;
    use integer::add as plus;

    #[test]
    fn cargo_renamed_facade_and_use_aliases_preserve_builtin_identity() {
        let application: plus = plus(integer::Int, integer::Int);
        let _: integer::add = application;

        assert_eq!(TypeId::of::<plus>(), TypeId::of::<k::builtin::int::add>());
        assert_eq!(
            k::builtin_registry().resolve_operation(TypeId::of::<plus>()),
            Some(BuiltinOperation::IntAdd)
        );
    }
}
