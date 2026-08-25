//! Executes the production metadata-plan/registration/collection/analysis path.

use std::collections::BTreeSet;
use std::env;
use std::error::Error;
use std::fs;
use std::io::{self, Write};

use krs_cli::{
    CargoMetadata, CollectorEntrypoint, CollectorPlan, CollectorRequest, FacetSelector,
    PackageSelector,
};
use krs_compiler::{analyze_open_sorts, collect_host_descriptors};
use krs_ir::{Descriptor, DescriptorBundle, DescriptorPayload};
use language_host::ItemKind;

// Deliberately explicit: linker retention must not depend on incidental imports.
#[allow(unused_extern_crates)]
extern crate author_root as _;
#[allow(unused_extern_crates)]
extern crate semantic_base as _;

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = env::args_os().skip(1);
    let metadata_path = args.next().ok_or("missing metadata JSON path")?;
    let selection_path = args.next().ok_or("missing canonical selection output path")?;
    let host_target = args
        .next()
        .ok_or("missing host target")?
        .into_string()
        .map_err(|_| "host target is not UTF-8")?;
    if args.next().is_some() {
        return Err("unexpected extra argument".into());
    }

    let metadata_bytes = fs::read(metadata_path)?;
    let metadata = CargoMetadata::from_json(&metadata_bytes)?;
    let plan = CollectorPlan::resolve(&metadata, &request(host_target))?;
    let selection = plan.canonical_selection_json()?;
    fs::write(selection_path, &selection)?;

    let contexts = plan.package_contexts()?;
    assert_eq!(contexts.len(), 2, "one context per selected semantics package");
    assert_eq!(
        contexts[0].crate_root(),
        "root_language_api",
        "custom [lib] target must be selected from Cargo metadata"
    );
    assert_eq!(contexts[1].crate_root(), "base_language_api");

    let host = language_host::host_descriptors().collect::<Vec<_>>();
    assert_eq!(host.len(), 24, "both explicitly linked packages must register");
    let bundle = collect_host_descriptors(contexts, host)?;
    assert_bundle(&bundle);
    let analysis = analyze_open_sorts(&bundle)?;
    assert_analysis(&bundle, &analysis);

    io::stdout().lock().write_all(bundle.to_canonical_json()?.as_bytes())?;
    Ok(())
}

fn request(host_target: String) -> CollectorRequest {
    CollectorRequest {
        root: FacetSelector {
            package: PackageSelector::Name("root-semantics".to_owned()),
            definition: "main".to_owned(),
        },
        dependencies: vec![FacetSelector {
            package: PackageSelector::Name("base-semantics".to_owned()),
            definition: "base".to_owned(),
        }],
        // Planning currently requires the entrypoint to be in the root closure.
        // This oracle invokes collection directly, so only reachability is relevant.
        entrypoint: CollectorEntrypoint {
            package: PackageSelector::Name("base-semantics".to_owned()),
            function: vec!["collector_anchor".to_owned()],
        },
        host_target,
        cfg: Vec::new(),
    }
}

fn assert_bundle(bundle: &DescriptorBundle) {
    assert_eq!(bundle.protocol_version().0, 4);
    assert_eq!(bundle.descriptors.len(), 24);

    let ids = bundle
        .descriptors
        .iter()
        .map(|descriptor| descriptor.id.clone())
        .collect::<BTreeSet<_>>();
    assert_eq!(ids.len(), bundle.descriptors.len());

    let same = bundle
        .descriptors
        .iter()
        .filter(|descriptor| {
            descriptor.id.item_name() == "Same"
                && descriptor.id.item_kind() == ItemKind::Constructor
        })
        .collect::<Vec<_>>();
    assert_eq!(same.len(), 4, "same-spelled constructors remain distinct");
    assert_eq!(
        same.iter()
            .map(|descriptor| descriptor.id.package().k_namespace())
            .collect::<BTreeSet<_>>()
            .len(),
        2,
        "same-spelled constructors span packages"
    );

    let common = bundle
        .descriptors
        .iter()
        .filter(|descriptor| {
            descriptor.id.item_name() == "Common" && descriptor.id.item_kind() == ItemKind::Sort
        })
        .count();
    assert_eq!(common, 4, "same-spelled sorts span modules and packages");

    let gap = descriptor(bundle, "ORG-KRS-M1-ROOT", &[], "ordinal_gap", ItemKind::Rule);
    let DescriptorPayload::Rule(gap) = &gap.payload else {
        panic!("ordinal_gap is a rule")
    };
    assert_eq!(gap.parameters[0].bindings, ["日本"]);
    let keys = gap
        .references
        .iter()
        .map(|reference| (reference.key.role(), reference.key.ordinal()))
        .collect::<BTreeSet<_>>();
    assert!(keys.contains(&("rule_left_path", 0)));
    assert!(keys.contains(&("rule_left_path", 2)));
    assert!(!keys.contains(&("rule_left_path", 1)));
    assert!(keys.contains(&("rule_right_path", 0)));
    assert!(!keys.contains(&("rule_right_path", 1)));
    assert!(keys.contains(&("rule_right_path", 2)));

    let native = descriptor(bundle, "ORG-KRS-M1-ROOT", &[], "native_swap", ItemKind::Rule);
    let DescriptorPayload::Rule(native) = &native.payload else {
        panic!("native_swap is a rule")
    };
    assert_eq!(native.parameters[0].bindings, ["first", "second"]);

    let zero = descriptor(bundle, "ORG-KRS-M1-ROOT", &[], "zero_bindings", ItemKind::Rule);
    let DescriptorPayload::Rule(zero) = &zero.payload else {
        panic!("zero_bindings is a rule")
    };
    assert!(zero.parameters[0].bindings.is_empty());

    let cross = descriptor(bundle, "ORG-KRS-M1-ROOT", &[], "cross_package", ItemKind::Rule);
    let DescriptorPayload::Rule(cross) = &cross.payload else {
        panic!("cross_package is a rule")
    };
    assert!(cross.references.iter().any(|reference| {
        reference.target.package().k_namespace() == "ORG-KRS-M1-BASE"
            && reference.target.item_name() == "Same"
    }));

    for descriptor in &bundle.descriptors {
        assert!(descriptor.origin.frames().len() >= 2);
        assert!(!descriptor.id.package().cargo_source().starts_with('/'));
    }
}

fn assert_analysis(
    bundle: &DescriptorBundle,
    analysis: &krs_compiler::OpenSortAnalysis,
) {
    let value = &descriptor(bundle, "ORG-KRS-M1-ROOT", &[], "Value", ItemKind::Sort).id;
    let kitem = &descriptor(bundle, "ORG-KRS-M1-ROOT", &[], "KItem", ItemKind::Sort).id;
    let value_node =
        &descriptor(bundle, "ORG-KRS-M1-ROOT", &[], "ValueNode", ItemKind::Constructor).id;
    let memberships = &analysis.member_sorts()[value_node];
    assert_eq!(memberships.len(), 4, "diamond closure must deduplicate KItem");
    assert!(memberships.contains(value));
    assert!(memberships.contains(kitem));
    assert_eq!(
        analysis.transitive_parents()[value]
            .iter()
            .filter(|parent| *parent == kitem)
            .count(),
        1,
        "closure is path-independent"
    );
}

fn descriptor<'a>(
    bundle: &'a DescriptorBundle,
    namespace: &str,
    module: &[&str],
    name: &str,
    kind: ItemKind,
) -> &'a Descriptor {
    bundle
        .descriptors
        .iter()
        .find(|descriptor| {
            descriptor.id.package().k_namespace() == namespace
                && descriptor.id.module_path().iter().map(String::as_str).eq(module.iter().copied())
                && descriptor.id.item_name() == name
                && descriptor.id.item_kind() == kind
        })
        .unwrap_or_else(|| panic!("missing {namespace}::{module:?}::{name}#{kind:?}"))
}
