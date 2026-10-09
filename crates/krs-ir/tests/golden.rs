//! Golden protocol and serialization-boundary tests.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::testing::{assert_canonical_contract, authored, item};
use krs_ir::{
    ConstructorDescriptor, ConstructorFieldDescriptor, Descriptor, DescriptorBundle,
    DescriptorDeclaration, DescriptorDeclarationError, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorProvenance, DescriptorProvenanceError, DescriptorSortRef, ExplicitSymbol,
    IdentityError, ItemKind, OriginFrame, OriginStack, OriginStackError, ProvenanceKey,
    ProvenanceRole, RangedOriginKind, RustVisibility, SchemaVersion, SortDescriptor, StableItemId,
    TransformationOriginKind,
};
use krs_test_support::{assert_rejects, assert_rejects_with_message};
use serde::Serialize;
use static_assertions::assert_not_impl_any;

fn origin() -> OriginStack {
    authored(0, 3)
}

fn descriptor(id: StableItemId, payload: DescriptorPayload) -> Descriptor {
    let role = match id.item_kind() {
        ItemKind::Sort => ProvenanceRole::SortDeclaration,
        ItemKind::Constructor => ProvenanceRole::ConstructorDeclaration,
        ItemKind::Configuration | ItemKind::Cell => ProvenanceRole::ConfigurationDeclaration,
        ItemKind::Grammar
        | ItemKind::Rule
        | ItemKind::Equation
        | ItemKind::Simplification
        | ItemKind::Claim
        | ItemKind::Alias
        | ItemKind::Desugar => ProvenanceRole::RuleDeclaration,
        ItemKind::ContextAlias => ProvenanceRole::ContextAliasDeclaration,
    };
    let primary_key = ProvenanceKey::new(role, 0);
    krs_ir::testing::descriptor(
        id,
        BTreeMap::new(),
        DescriptorProvenance::new(
            primary_key.clone(),
            vec![DescriptorNodeOrigin::new(primary_key, origin())],
        )
        .unwrap(),
        payload,
    )
}

fn populated_bundle() -> DescriptorBundle {
    let k_item = item("syntax", "KItem", ItemKind::Sort);
    let value = item("syntax", "Value", ItemKind::Sort);
    let foo_constructor = item("syntax", "Foo", ItemKind::Constructor);
    let bar_constructor = item("syntax", "Bar", ItemKind::Constructor);

    let sort = descriptor(
        value.clone(),
        DescriptorPayload::Sort(SortDescriptor {
            parents: BTreeSet::from([k_item.clone()]),
        }),
    );
    let constructor = descriptor(
        foo_constructor,
        DescriptorPayload::Constructor(ConstructorDescriptor {
            sort: DescriptorSortRef::Declared(value.clone()),
            fields: vec![ConstructorFieldDescriptor {
                name: "value".into(),
                sort: Some(DescriptorSortRef::Declared(k_item)),
            }],
        }),
    );
    let bar = descriptor(
        bar_constructor,
        DescriptorPayload::Constructor(ConstructorDescriptor {
            sort: DescriptorSortRef::Declared(value),
            fields: Vec::new(),
        }),
    );

    let bundle = DescriptorBundle::new(vec![bar, sort, constructor]).unwrap();
    assert_canonical_contract(&bundle);
    bundle
}

#[test]
fn empty_bundle_matches_golden() {
    assert_canonical_contract(&DescriptorBundle::empty());
    expect_test::expect_file!["golden/empty_bundle.json"]
        .assert_eq(&DescriptorBundle::empty().to_canonical_json().unwrap());
}

#[test]
fn populated_bundle_matches_golden() {
    assert_canonical_contract(&populated_bundle());
    expect_test::expect_file!["golden/sort_constructors.json"]
        .assert_eq(&populated_bundle().to_canonical_json().unwrap());
}

#[test]
fn collector_protocol_matches_goldens_and_counts_provenance_values() {
    let empty = DescriptorBundle::empty();
    let mut empty_bytes = Vec::new();
    empty.write_collector_protocol(&mut empty_bytes).unwrap();
    expect_test::expect_file!["golden/collector_empty_bundle.json"]
        .assert_eq(std::str::from_utf8(&empty_bytes).unwrap());

    let bundle = populated_bundle();
    let owned = bundle.clone();
    let (bytes, provenance) = owned.to_collector_protocol_measured().unwrap();
    expect_test::expect_file!["golden/collector_sort_constructors.json"]
        .assert_eq(std::str::from_utf8(&bytes).unwrap());
    let mut streamed = Vec::new();
    bundle
        .clone()
        .write_collector_protocol(&mut streamed)
        .unwrap();
    assert_eq!(streamed, bytes);
    let decoded = DescriptorBundle::from_collector_protocol(&bytes).unwrap();
    assert_eq!(
        decoded.to_canonical_json().unwrap(),
        owned.to_canonical_json().unwrap()
    );
    let parsed: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let expected: usize = parsed["descriptors"]
        .as_array()
        .unwrap()
        .iter()
        .map(|descriptor| serde_json::to_vec(&descriptor["provenance"]).unwrap().len())
        .sum();
    assert!(expected > 0);
    assert_eq!(provenance, u64::try_from(expected).unwrap());
}

#[test]
fn collector_wire_preserves_every_frame_kind_and_rejects_bad_references() {
    let mut descriptors = populated_bundle()
        .descriptors()
        .iter()
        .cloned()
        .map(krs_ir::testing::DescriptorInputs::from)
        .collect::<Vec<_>>();
    let descriptor = &mut descriptors[0];
    let id = descriptor.id.clone();
    let mut stack = origin();
    let range = match &stack.frames()[0] {
        OriginFrame::Ranged { range, .. } => range.clone(),
        OriginFrame::Transformation { .. } => unreachable!(),
    };
    for kind in [
        RangedOriginKind::MacroInvocation,
        RangedOriginKind::GeneratedArtifact,
        RangedOriginKind::FrontendDiagnostic,
    ] {
        stack.push(OriginFrame::Ranged {
            kind,
            range: range.clone(),
            item: Some(id.clone()),
            label: Some("preserved".to_owned()),
        });
    }
    for kind in [
        TransformationOriginKind::GeneratedDescriptor,
        TransformationOriginKind::SemanticIr,
        TransformationOriginKind::DefinitionIr,
    ] {
        stack.push(OriginFrame::Transformation {
            kind,
            item: Some(id.clone()),
            label: Some("preserved".to_owned()),
        });
    }
    let key = descriptor.provenance.primary_key().clone();
    descriptor.provenance =
        DescriptorProvenance::new(key.clone(), vec![DescriptorNodeOrigin::new(key, stack)])
            .unwrap();
    let bundle = krs_ir::testing::descriptor_bundle(descriptors).unwrap();
    assert_canonical_contract(&bundle);
    let bytes = bundle.to_collector_protocol_measured().unwrap().0;
    let decoded = DescriptorBundle::from_collector_protocol(&bytes).unwrap();
    assert_eq!(decoded, bundle);

    let mut wire: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let mut short = wire.clone();
    short["descriptors"][0]["provenance"]["origins"][0]["origin"][1]
        .as_array_mut()
        .unwrap()
        .pop();
    assert_rejects_with_message(
        DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&short).unwrap()),
        "invalid length 5, expected a collector frame array",
    );
    let mut long = wire.clone();
    long["descriptors"][0]["provenance"]["origins"][0]["origin"][1]
        .as_array_mut()
        .unwrap()
        .push(serde_json::Value::Null);
    assert_rejects_with_message(
        DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&long).unwrap()),
        "collector frame has extra fields",
    );
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][1] = 999.into();
    let bad_file = serde_json::to_vec(&wire).unwrap();
    assert_rejects_with_message(
        DescriptorBundle::from_collector_protocol(&bad_file),
        "invalid file index 999",
    );
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][1] = 0.into();
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][4] = 999.into();
    let bad_item = serde_json::to_vec(&wire).unwrap();
    assert_rejects_with_message(
        DescriptorBundle::from_collector_protocol(&bad_item),
        "invalid item index 999",
    );
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][4] = 0.into();
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][0] = 99.into();
    let bad_code = serde_json::to_vec(&wire).unwrap();
    assert_rejects_with_message(
        DescriptorBundle::from_collector_protocol(&bad_code),
        "unknown collector frame code 99",
    );
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][0] = 1.into();
}

#[test]
fn canonical_json_ignores_insertion_order() {
    assert_canonical_contract(&populated_bundle());
}

#[test]
fn collector_table_errors_precede_descriptor_contract_errors() {
    let bytes = populated_bundle()
        .to_collector_protocol_measured()
        .unwrap()
        .0;
    let mut wire: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    wire["descriptors"][2]["provenance"]["origins"][0]["origin"][0][1] = serde_json::json!(99999);
    let expected = DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&wire).unwrap())
        .unwrap_err()
        .to_string();
    assert_eq!(expected, "invalid file index 99999");
    wire["descriptors"][0]["id"]["item_kind"] = serde_json::json!("sort");
    let actual = DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&wire).unwrap())
        .unwrap_err()
        .to_string();
    assert_eq!(actual, expected);
}

#[test]
fn declaration_metadata_requires_exact_descriptor_coverage() {
    let bundle = populated_bundle();
    let declarations = || {
        bundle
            .descriptors()
            .iter()
            .map(|descriptor| {
                DescriptorDeclaration::new(descriptor.id().clone(), RustVisibility::Inherited, None)
            })
            .collect::<Vec<_>>()
    };

    let mut missing = declarations();
    let missing_id = missing.pop().unwrap().id().clone();
    assert_eq!(
        DescriptorBundle::with_declarations(bundle.descriptors().to_vec(), missing),
        Err(DescriptorDeclarationError::Missing(Box::new(missing_id)))
    );

    let mut extra = declarations();
    let extra_id = item("syntax", "Extra", ItemKind::Sort);
    extra.push(DescriptorDeclaration::new(
        extra_id.clone(),
        RustVisibility::Inherited,
        None,
    ));
    assert_eq!(
        DescriptorBundle::with_declarations(bundle.descriptors().to_vec(), extra),
        Err(DescriptorDeclarationError::Extra(Box::new(extra_id)))
    );

    let mut duplicate = declarations();
    let duplicate_id = duplicate[0].id().clone();
    duplicate.push(duplicate[0].clone());
    assert_eq!(
        DescriptorBundle::with_declarations(bundle.descriptors().to_vec(), duplicate),
        Err(DescriptorDeclarationError::Duplicate(Box::new(
            duplicate_id
        )))
    );
}

#[test]
fn explicit_symbol_metadata_and_parser_provenance_must_agree() {
    let bundle = populated_bundle();
    let pinned_id = bundle.descriptors()[0].id().clone();
    let mut declarations = bundle.declarations().to_vec();
    declarations[0] = DescriptorDeclaration::new(
        pinned_id.clone(),
        RustVisibility::Inherited,
        Some(ExplicitSymbol::new("api::Pinned").unwrap()),
    );
    assert_eq!(
        DescriptorBundle::with_declarations(bundle.descriptors().to_vec(), declarations),
        Err(DescriptorDeclarationError::MissingSymbolOrigin(Box::new(
            pinned_id.clone(),
        )))
    );

    let mut descriptors = bundle
        .descriptors()
        .iter()
        .cloned()
        .map(krs_ir::testing::DescriptorInputs::from)
        .collect::<Vec<_>>();
    let primary_key = descriptors[0].provenance.primary_key().clone();
    let mut origins = descriptors[0].provenance.origins().to_vec();
    origins.push(DescriptorNodeOrigin::new(
        ProvenanceKey::new(ProvenanceRole::StableSymbol, 0),
        origin(),
    ));
    descriptors[0].provenance = DescriptorProvenance::new(primary_key, origins).unwrap();
    assert_eq!(
        DescriptorBundle::with_declarations(
            descriptors
                .iter()
                .map(|input| input.build().unwrap())
                .collect(),
            bundle.declarations().to_vec()
        ),
        Err(DescriptorDeclarationError::UnexpectedSymbolOrigin(
            Box::new(pinned_id,)
        ))
    );
}

#[test]
fn restricted_visibility_wire_data_is_exact_and_validated() {
    let shorthand = RustVisibility::restricted("crate", false).unwrap();
    let explicit = RustVisibility::restricted("crate", true).unwrap();
    assert_ne!(shorthand, explicit);
    assert_eq!(
        serde_json::to_value(shorthand).unwrap(),
        serde_json::json!({
            "visibility": "restricted",
            "path": "crate",
            "explicit_in": false
        })
    );
    assert_eq!(
        serde_json::to_value(explicit).unwrap(),
        serde_json::json!({
            "visibility": "restricted",
            "path": "crate",
            "explicit_in": true
        })
    );

    for (path, expected_kind) in [
        ("", IdentityError::InvalidVisibilityPath(String::new())),
        (
            "crate::::private",
            IdentityError::InvalidVisibilityPath("crate::::private".into()),
        ),
        (
            "crate/private",
            IdentityError::InvalidVisibilityPath("crate/private".into()),
        ),
        (
            "crate\\private",
            IdentityError::InvalidVisibilityPath("crate\\private".into()),
        ),
    ] {
        let wire = serde_json::json!({
            "visibility": "restricted",
            "path": path,
            "explicit_in": false
        });
        assert_rejects_with_message(
            serde_json::from_value::<RustVisibility>(wire),
            expected_kind,
        );
    }
}

#[test]
fn bundles_reject_duplicate_identities_even_when_payloads_differ() {
    let bundle = populated_bundle();
    let mut descriptors = bundle.descriptors().to_vec();
    let mut alternate = krs_ir::testing::DescriptorInputs::from(descriptors[0].clone());
    if let DescriptorPayload::Constructor(constructor) = &mut alternate.payload {
        constructor.fields.push(ConstructorFieldDescriptor {
            name: "alternate".into(),
            sort: None,
        });
    }
    descriptors.push(alternate.build().unwrap());
    let expected =
        DescriptorDeclarationError::DuplicateIdentity(Box::new(descriptors[0].id().clone()));
    assert_eq!(
        DescriptorBundle::new(descriptors.clone()),
        Err(expected.clone())
    );
    let mut json = serde_json::to_value(&bundle).unwrap();
    let duplicated = json["descriptors"][0].clone();
    json["descriptors"].as_array_mut().unwrap().push(duplicated);
    assert_rejects_with_message(
        serde_json::from_value::<DescriptorBundle>(json),
        expected.clone(),
    );
    descriptors.reverse();
    assert_eq!(DescriptorBundle::new(descriptors), Err(expected));
}

#[test]
fn canonical_json_orders_parser_keyed_origins_without_changing_primary() {
    let primary_key = ProvenanceKey::new(ProvenanceRole::ConstructorDeclaration, 0);
    let nested_key = ProvenanceKey::new(ProvenanceRole::ConstructorFieldDeclaration, 0);
    let mut descriptors = populated_bundle()
        .descriptors()
        .iter()
        .cloned()
        .map(krs_ir::testing::DescriptorInputs::from)
        .collect::<Vec<_>>();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Constructor)
        .unwrap();
    descriptor.provenance = DescriptorProvenance::new(
        primary_key.clone(),
        vec![
            DescriptorNodeOrigin::new(nested_key.clone(), origin()),
            DescriptorNodeOrigin::new(primary_key.clone(), origin()),
        ],
    )
    .unwrap();

    let forward = krs_ir::testing::descriptor_bundle(descriptors).unwrap();
    assert_canonical_contract(&forward);
    let mut ordered_descriptors = forward
        .descriptors()
        .iter()
        .cloned()
        .map(krs_ir::testing::DescriptorInputs::from)
        .collect::<Vec<_>>();
    ordered_descriptors
        .iter_mut()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Constructor)
        .unwrap()
        .provenance = DescriptorProvenance::new(
        primary_key.clone(),
        vec![
            DescriptorNodeOrigin::new(primary_key.clone(), origin()),
            DescriptorNodeOrigin::new(nested_key, origin()),
        ],
    )
    .unwrap();
    let ordered = krs_ir::testing::descriptor_bundle(ordered_descriptors).unwrap();
    assert_canonical_contract(&ordered);
    assert_eq!(
        forward.to_canonical_json().unwrap(),
        ordered.to_canonical_json().unwrap()
    );
    let descriptor = forward
        .descriptors()
        .iter()
        .find(|descriptor| descriptor.id().item_kind() == ItemKind::Constructor)
        .unwrap();
    assert_eq!(descriptor.provenance().primary_key(), &primary_key);
    assert_eq!(
        descriptor.origin(),
        descriptor.provenance().primary_origin()
    );

    let round_trip: DescriptorBundle =
        serde_json::from_str(&forward.to_canonical_json().unwrap()).unwrap();
    let constructor = round_trip
        .descriptors()
        .iter()
        .find(|descriptor| descriptor.id().item_kind() == ItemKind::Constructor)
        .unwrap();
    assert!(
        constructor
            .provenance()
            .origin_for(&ProvenanceKey::new(
                ProvenanceRole::ConstructorFieldDeclaration,
                0
            ))
            .is_some(),
        "an exact nested parser-keyed origin survives a round trip"
    );
}

#[test]
fn descriptor_provenance_rejects_empty_duplicate_and_missing_primary_tables() {
    let primary = ProvenanceKey::new(ProvenanceRole::RuleDeclaration, 0);
    let nested = ProvenanceKey::new(ProvenanceRole::RuleRightPath, 0);
    assert_rejects!(
        DescriptorProvenance::new(primary.clone(), Vec::new()),
        DescriptorProvenanceError::Empty
    );
    assert_rejects!(
        DescriptorProvenance::new(
            primary.clone(),
            vec![DescriptorNodeOrigin::new(nested, origin())]
        ),
        DescriptorProvenanceError::MissingPrimary(key) if key == primary
    );
    assert_rejects!(
        DescriptorProvenance::new(
            primary.clone(),
            vec![
                DescriptorNodeOrigin::new(primary.clone(), origin()),
                DescriptorNodeOrigin::new(primary.clone(), origin()),
            ]
        ),
        DescriptorProvenanceError::DuplicateKey(key) if key == primary
    );
}

#[test]
fn descriptor_provenance_rejects_unknown_wire_fields() {
    let value = serde_json::json!({
        "primary_key": { "role": "sort_declaration", "ordinal": 0 },
        "origins": [{
            "key": { "role": "sort_declaration", "ordinal": 0 },
            "origin": serde_json::to_value(origin()).unwrap(),
            "unexpected": true
        }]
    });
    let error = serde_json::from_value::<DescriptorProvenance>(value).unwrap_err();
    assert!(error.to_string().contains("unexpected"));

    let top_level = serde_json::json!({
        "protocol_version": SchemaVersion::CURRENT.0,
        "descriptors": [],
        "declarations": [],
        "unexpected": true
    });
    let error = serde_json::from_value::<DescriptorBundle>(top_level).unwrap_err();
    assert!(error.to_string().contains("unexpected"));
}

#[test]
fn host_only_values_cannot_implement_serialization() {
    assert_not_impl_any!(krs_ir::HostTypeKey: Serialize);
    assert_not_impl_any!(krs_ir::HostDescriptor: Serialize);
    assert_not_impl_any!(krs_ir::HostSourceAnchor: Serialize);
    assert_not_impl_any!(krs_ir::HostProvenance: Serialize);
    assert_not_impl_any!(krs_ir::HostPackageKey: Serialize);
    assert_not_impl_any!(krs_ir::HostItemId: Serialize);
    assert_not_impl_any!(krs_ir::HostConstructorFieldDescriptor: Serialize);
}

#[test]
fn provenance_keys_round_trip_with_validation() {
    let key = ProvenanceKey::new(ProvenanceRole::RuleRightPath, 7);
    let json = serde_json::to_string(&key).unwrap();
    assert_eq!(serde_json::from_str::<ProvenanceKey>(&json).unwrap(), key);
    assert_rejects_with_message(
        serde_json::from_str::<ProvenanceKey>(r#"{"role":"","ordinal":0}"#),
        "unknown provenance role ``",
    );
}

#[test]
fn empty_origin_stack_is_rejected_at_the_protocol_boundary() {
    assert_rejects_with_message(
        serde_json::from_str::<OriginStack>("[]"),
        OriginStackError::Empty,
    );
}

#[test]
fn transformation_frames_have_no_fabricated_range() {
    let mut origin = origin();
    origin.push(OriginFrame::Transformation {
        kind: TransformationOriginKind::SemanticIr,
        item: None,
        label: Some("sort-closure-node".into()),
    });
    let json = serde_json::to_value(origin).unwrap();
    let transformation = &json.as_array().unwrap()[1];
    assert_eq!(transformation["frame_type"], "transformation");
    assert!(transformation.get("range").is_none());
}

#[test]
fn transformation_frame_cannot_begin_an_origin_stack() {
    let json = r#"[{
        "frame_type":"transformation",
        "kind":"generated_descriptor",
        "label":"payload"
    }]"#;
    assert_rejects_with_message(
        serde_json::from_str::<OriginStack>(json),
        OriginStackError::FirstFrameNotAuthored,
    );
}
