//! Target-neutral open-sort analysis tests.

use std::collections::BTreeMap;

use krs_compiler::{AnalysisErrorKind, analyze_open_sorts};
use krs_ir::testing;
use krs_ir::{
    ConstructorDescriptor, Descriptor, DescriptorBundle, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorProvenance, ItemKind, OriginStack, PackageId, ProvenanceKey, ProvenanceRole,
    SortDescriptor, StableItemId,
};

#[test]
fn diamond_closure_and_constructor_membership_are_path_independent() {
    let kitem = id("KItem", ItemKind::Sort);
    let expr = id("Expr", ItemKind::Sort);
    let kresult = id("KResult", ItemKind::Sort);
    let value = id("Value", ItemKind::Sort);
    let integer = id("IntValue", ItemKind::Constructor);
    let bundle = DescriptorBundle::new(vec![
        sort(kitem.clone(), vec![]),
        sort(expr.clone(), vec![kitem.clone()]),
        sort(kresult.clone(), vec![kitem.clone()]),
        sort(value.clone(), vec![expr.clone(), kresult.clone()]),
        constructor(integer.clone(), value.clone()),
    ]);

    let analysis = analyze_open_sorts(&bundle).unwrap();
    assert_eq!(
        analysis.transitive_parents()[&value],
        vec![expr.clone(), kitem.clone(), kresult.clone()]
    );
    assert_eq!(analysis.member_sorts()[&integer].len(), 4);
    assert_eq!(analysis.constructors_by_sort()[&kitem], vec![integer]);
}

#[test]
fn modeled_blanket_impl_counterexample_still_has_one_compiler_owned_join() {
    let top = id("Top", ItemKind::Sort);
    let left = id("Left", ItemKind::Sort);
    let right = id("Right", ItemKind::Sort);
    let bottom = id("Bottom", ItemKind::Sort);
    let item = id("Item", ItemKind::Constructor);
    let bundle = DescriptorBundle::new(vec![
        sort(top.clone(), vec![]),
        sort(left.clone(), vec![top.clone()]),
        sort(right.clone(), vec![top.clone()]),
        sort(bottom.clone(), vec![left, right]),
        constructor(item.clone(), bottom),
    ]);

    let analysis = analyze_open_sorts(&bundle).unwrap();
    let top_count = analysis.member_sorts()[&item]
        .iter()
        .filter(|sort| *sort == &top)
        .count();
    assert_eq!(
        top_count, 1,
        "diamond paths must not become Rust impl paths"
    );
}

#[test]
fn cycles_unresolved_edges_and_wrong_kinds_are_rejected() {
    let a = id("A", ItemKind::Sort);
    let b = id("B", ItemKind::Sort);
    let cycle = DescriptorBundle::new(vec![
        sort(a.clone(), vec![b.clone()]),
        sort(b.clone(), vec![a]),
    ]);
    assert_eq!(
        analyze_open_sorts(&cycle).unwrap_err().kind(),
        AnalysisErrorKind::SortCycle
    );

    let missing = id("Missing", ItemKind::Sort);
    let unresolved = DescriptorBundle::new(vec![sort(b.clone(), vec![missing])]);
    assert_eq!(
        analyze_open_sorts(&unresolved).unwrap_err().kind(),
        AnalysisErrorKind::UnresolvedReference
    );

    let constructor_id = id("Ctor", ItemKind::Constructor);
    let wrong = DescriptorBundle::new(vec![
        sort(b, vec![constructor_id.clone()]),
        constructor(constructor_id, id("Sort", ItemKind::Sort)),
    ]);
    assert_eq!(
        analyze_open_sorts(&wrong).unwrap_err().kind(),
        AnalysisErrorKind::ReferenceKindMismatch
    );
}

#[test]
fn duplicate_serialized_ids_are_rejected_before_analysis() {
    let sort_id = id("Expr", ItemKind::Sort);
    let descriptor = sort(sort_id, vec![]);
    let bundle = DescriptorBundle::new(vec![descriptor.clone(), descriptor]);
    assert_eq!(
        analyze_open_sorts(&bundle).unwrap_err().kind(),
        AnalysisErrorKind::DuplicateItemId
    );
}

fn package() -> PackageId {
    testing::package("ORG-SEMANTIC", "semantic")
}

fn id(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "model", name, kind)
}

fn origin() -> OriginStack {
    testing::authored_in(
        package(),
        "src/lib.rs",
        testing::digest_with("a".repeat(64)),
        0,
        1,
    )
}

fn sort(id: StableItemId, parents: Vec<StableItemId>) -> Descriptor {
    Descriptor {
        id,
        cfg: BTreeMap::new(),
        provenance: provenance(ProvenanceRole::SortDeclaration),
        payload: DescriptorPayload::Sort(SortDescriptor { parents }),
    }
}

fn constructor(id: StableItemId, sort: StableItemId) -> Descriptor {
    Descriptor {
        id,
        cfg: BTreeMap::new(),
        provenance: provenance(ProvenanceRole::ConstructorSort),
        payload: DescriptorPayload::Constructor(ConstructorDescriptor {
            sort: krs_ir::DescriptorSortRef::Declared(sort),
            syntax: None,
            fields: Vec::new(),
        }),
    }
}

fn provenance(role: ProvenanceRole) -> DescriptorProvenance {
    let key = ProvenanceKey::new(role, 0);
    DescriptorProvenance::new(key.clone(), vec![DescriptorNodeOrigin::new(key, origin())]).unwrap()
}
