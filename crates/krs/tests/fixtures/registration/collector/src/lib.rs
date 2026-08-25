//! Explicit collector-root fixture spanning nested modules and a dependency.

use std::collections::BTreeMap;

use k::{
    AnchorPrecision, HostAuthoredAnchor, HostDescriptor, HostDescriptorPayload, HostProvenance,
    HostSortDescriptor, HostSourceAnchor, HostSourcePosition, ItemKind, PackageId, ProtocolVersion,
    ProvenanceKey, StableItemId,
};

mod nested {
    use super::{HostDescriptor, descriptor};

    fn nested_descriptor() -> HostDescriptor {
        descriptor(&["nested"], "NestedSort")
    }

    k::__register_host_descriptor!(nested_descriptor);

    mod deeper {
        use super::{HostDescriptor, descriptor};

        fn deeper_descriptor() -> HostDescriptor {
            descriptor(&["nested", "deeper"], "DeeperSort")
        }

        k::__register_host_descriptor!(deeper_descriptor);
    }
}

fn descriptor(module: &[&str], item: &str) -> HostDescriptor {
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
        id: StableItemId::new(
            PackageId::new("ORG-COLLECTOR", "registration-collector", "0.0.0", "workspace")
                .expect("valid package"),
            module.iter().copied(),
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

/// Enumerates descriptors after explicitly retaining selected dependencies.
///
/// The returned vector preserves no meaningful order. The real collector must
/// resolve and sort stable identities before producing its serializable IR.
#[must_use]
pub fn collect_selected_host_descriptors() -> Vec<HostDescriptor> {
    semantics_dependency::retain_for_krs_collector();
    k::host_descriptors().collect()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::collect_selected_host_descriptors;

    #[test]
    fn explicit_root_retains_nested_and_dependency_registrations() {
        let identities = collect_selected_host_descriptors()
            .into_iter()
            .map(|descriptor| {
                (
                    descriptor.id.package().k_namespace().to_owned(),
                    descriptor.id.module_path().to_vec(),
                    descriptor.id.item_name().to_owned(),
                )
            })
            .collect::<BTreeSet<_>>();

        assert!(identities.contains(&(
            "ORG-COLLECTOR".to_owned(),
            vec!["nested".to_owned()],
            "NestedSort".to_owned(),
        )));
        assert!(identities.contains(&(
            "ORG-COLLECTOR".to_owned(),
            vec!["nested".to_owned(), "deeper".to_owned()],
            "DeeperSort".to_owned(),
        )));
        assert!(identities.contains(&(
            "ORG-DEPENDENCY".to_owned(),
            vec!["dependency".to_owned()],
            "DependencySort".to_owned(),
        )));
    }
}
