//! Pin the collector encoding sample beside `collector::VERSION`.
//! A collector file change must advance `collector::VERSION` and its `Krs.lock` entry;
//! a released version's file must never be overwritten.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use krs_ir::transport::collector;
use krs_ir::{
    ConstructorDescriptor, ConstructorFieldDescriptor, Descriptor, DescriptorBundle,
    DescriptorDeclaration, DescriptorNodeOrigin, DescriptorPayload, DescriptorProvenance,
    DescriptorSortRef, ExplicitSymbol, ItemKind, OriginFrame, OriginStack, ProvenanceKey,
    ProvenanceRole, RangedOriginKind, RustVisibility, SortDescriptor, StableItemId,
    TransformationOriginKind,
};
use krs_test_support::assert_versioned_pin;

fn collector_origin(id: &StableItemId, populated: bool) -> OriginStack {
    let authored = krs_ir::testing::authored(0, 3);
    let range = match &authored.frames()[0] {
        OriginFrame::Ranged { range, .. } => range.clone(),
        OriginFrame::Transformation { .. } => unreachable!(),
    };
    let item = populated.then(|| id.clone());
    let label = populated.then(|| "collector schema sample".to_owned());
    let mut frames = vec![OriginFrame::Ranged {
        kind: RangedOriginKind::Authored,
        range: range.clone(),
        item: item.clone(),
        label: label.clone(),
    }];
    for kind in [
        RangedOriginKind::MacroInvocation,
        RangedOriginKind::GeneratedArtifact,
        RangedOriginKind::FrontendDiagnostic,
    ] {
        frames.push(OriginFrame::Ranged {
            kind,
            range: range.clone(),
            item: item.clone(),
            label: label.clone(),
        });
    }
    for kind in [
        TransformationOriginKind::GeneratedDescriptor,
        TransformationOriginKind::SemanticIr,
        TransformationOriginKind::DefinitionIr,
    ] {
        frames.push(OriginFrame::Transformation {
            kind,
            item: item.clone(),
            label: label.clone(),
        });
    }
    OriginStack::try_from_frames(frames).unwrap()
}

fn collector_descriptor(
    id: StableItemId,
    payload: DescriptorPayload,
    populated: bool,
) -> Descriptor {
    let role = match id.item_kind() {
        ItemKind::Sort => ProvenanceRole::SortDeclaration,
        ItemKind::Constructor => ProvenanceRole::ConstructorDeclaration,
        _ => unreachable!(),
    };
    let key = ProvenanceKey::new(role, 0);
    let mut origins = vec![DescriptorNodeOrigin::new(
        key.clone(),
        collector_origin(&id, populated),
    )];
    if populated {
        origins.push(DescriptorNodeOrigin::new(
            ProvenanceKey::new(ProvenanceRole::StableSymbol, 0),
            krs_ir::testing::authored(0, 3),
        ));
    }
    krs_ir::testing::descriptor(
        id,
        BTreeMap::from([("feature".to_owned(), Some("enabled".to_owned()))]),
        DescriptorProvenance::new(key, origins).unwrap(),
        payload,
    )
}

#[test]
fn collector_encoding_is_pinned() {
    let sort_id = krs_ir::testing::item("syntax", "Value", ItemKind::Sort);
    let constructor_id = krs_ir::testing::item("syntax", "Foo", ItemKind::Constructor);
    let sort = collector_descriptor(
        sort_id.clone(),
        DescriptorPayload::Sort(SortDescriptor {
            parents: BTreeSet::new(),
        }),
        true,
    );
    let constructor = collector_descriptor(
        constructor_id.clone(),
        DescriptorPayload::Constructor(ConstructorDescriptor {
            sort: DescriptorSortRef::Declared(sort_id.clone()),
            fields: vec![ConstructorFieldDescriptor {
                name: "value".to_owned(),
                sort: Some(DescriptorSortRef::Declared(sort_id)),
            }],
        }),
        false,
    );
    let bundle = DescriptorBundle::with_declarations(
        vec![sort, constructor],
        vec![
            DescriptorDeclaration::new(
                krs_ir::testing::item("syntax", "Value", ItemKind::Sort),
                RustVisibility::Public,
                Some(ExplicitSymbol::new("Schema::Value").unwrap()),
            ),
            DescriptorDeclaration::new(constructor_id, RustVisibility::Inherited, None),
        ],
    )
    .unwrap();
    let bytes = bundle.to_collector_protocol_measured().unwrap().0;
    let decoded = DescriptorBundle::from_collector_protocol(&bytes).unwrap();
    assert_eq!(decoded, bundle);
    let encoded: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let frame_codes: BTreeSet<_> = encoded["descriptors"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|descriptor| descriptor["provenance"]["origins"].as_array().unwrap())
        .flat_map(|origin| origin["origin"].as_array().unwrap())
        .map(|frame| frame[0].as_u64().unwrap())
        .collect();
    assert_eq!(frame_codes, (0..=6).collect());

    let actual = format!("{}\n", serde_json::to_string_pretty(&encoded).unwrap());
    assert_versioned_pin(
        Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests")),
        &format!("schema/collector-{}.json", collector::VERSION),
        "collector::VERSION and Krs.lock [schemas] collector",
        &actual,
    );
}
