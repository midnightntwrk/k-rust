//! Golden protocol and serialization-boundary tests.

use std::collections::BTreeMap;

use krs_ir::testing::{authored, item};
use krs_ir::transport::collector;
use krs_ir::{
    ConstructorDescriptor, ConstructorFieldDescriptor, Descriptor, DescriptorBundle,
    DescriptorDeclaration, DescriptorDeclarationError, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorProvenance, DescriptorSortRef, ExplicitSymbol, ItemKind, OriginFrame, OriginStack,
    ProvenanceKey, RangedOriginKind, RustVisibility, SchemaVersion, SortDescriptor, StableItemId,
    TransformationOriginKind,
};
use serde::Serialize;
use static_assertions::assert_not_impl_any;

fn origin() -> OriginStack {
    authored(0, 3)
}

fn descriptor(id: StableItemId, payload: DescriptorPayload) -> Descriptor {
    let role = match id.item_kind() {
        ItemKind::Sort => "sort_declaration",
        ItemKind::Constructor => "constructor_declaration",
        ItemKind::Grammar => "grammar_declaration",
        ItemKind::Configuration | ItemKind::Cell => "configuration_declaration",
        ItemKind::Rule
        | ItemKind::Equation
        | ItemKind::Simplification
        | ItemKind::Claim
        | ItemKind::Alias => "rule_declaration",
        ItemKind::ContextAlias => "context_alias_declaration",
    };
    let primary_key = ProvenanceKey::new(role, 0).unwrap();
    Descriptor {
        id,
        cfg: BTreeMap::new(),
        provenance: DescriptorProvenance::new(
            primary_key.clone(),
            vec![DescriptorNodeOrigin::new(primary_key, origin())],
        )
        .unwrap(),
        payload,
    }
}

fn populated_bundle(reverse: bool) -> DescriptorBundle {
    let k_item = item("syntax", "KItem", ItemKind::Sort);
    let value = item("syntax", "Value", ItemKind::Sort);
    let foo_constructor = item("syntax", "Foo", ItemKind::Constructor);
    let bar_constructor = item("syntax", "Bar", ItemKind::Constructor);

    let sort = descriptor(
        value.clone(),
        DescriptorPayload::Sort(SortDescriptor {
            // Parent insertion is intentionally non-canonical.
            parents: vec![k_item.clone(), k_item.clone()],
        }),
    );
    let constructor = descriptor(
        foo_constructor,
        DescriptorPayload::Constructor(ConstructorDescriptor {
            sort: DescriptorSortRef::Declared(value.clone()),
            syntax: Some("foo({value})".into()),
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
            syntax: Some("bar".into()),
            fields: Vec::new(),
        }),
    );

    let mut descriptors = vec![bar, sort, constructor];
    if reverse {
        descriptors.reverse();
    }
    DescriptorBundle::new(descriptors)
}

#[test]
fn empty_bundle_matches_golden() {
    expect_test::expect_file!["golden/empty_bundle.json"]
        .assert_eq(&DescriptorBundle::empty().to_canonical_json().unwrap());
}

#[test]
fn prior_protocols_have_no_compatibility_reader() {
    let draft_v1 = r#"{"protocol_version":1,"descriptors":[]}"#;
    let draft_v2 = r#"{"protocol_version":2,"descriptors":[]}"#;
    let draft_v3 = r#"{"protocol_version":3,"descriptors":[]}"#;
    let draft_v4 = r#"{"protocol_version":4,"descriptors":[]}"#;
    assert!(serde_json::from_str::<DescriptorBundle>(draft_v1).is_err());
    assert!(serde_json::from_str::<DescriptorBundle>(draft_v2).is_err());
    assert!(serde_json::from_str::<DescriptorBundle>(draft_v3).is_err());
    assert!(serde_json::from_str::<DescriptorBundle>(draft_v4).is_err());
}

#[test]
fn populated_bundle_matches_golden() {
    expect_test::expect_file!["golden/sort_constructors.json"]
        .assert_eq(&populated_bundle(false).to_canonical_json().unwrap());
}

#[test]
fn collector_protocol_matches_goldens_and_counts_provenance_values() {
    let mut empty = DescriptorBundle::empty();
    let mut empty_bytes = Vec::new();
    empty
        .write_collector_protocol_in_place(&mut empty_bytes)
        .unwrap();
    expect_test::expect_file!["golden/collector_empty_bundle.json"]
        .assert_eq(std::str::from_utf8(&empty_bytes).unwrap());

    let bundle = populated_bundle(false);
    let mut owned = bundle.clone();
    let (bytes, provenance) = owned.to_collector_protocol_measured_in_place().unwrap();
    expect_test::expect_file!["golden/collector_sort_constructors.json"]
        .assert_eq(std::str::from_utf8(&bytes).unwrap());
    let mut streamed = Vec::new();
    bundle
        .clone()
        .write_collector_protocol_in_place(&mut streamed)
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
    let mut bundle = populated_bundle(false);
    let descriptor = &mut bundle.descriptors[0];
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
    let bytes = bundle.to_collector_protocol_measured_in_place().unwrap().0;
    let decoded = DescriptorBundle::from_collector_protocol(&bytes).unwrap();
    assert_eq!(decoded, bundle);

    let mut wire: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let mut short = wire.clone();
    short["descriptors"][0]["provenance"]["origins"][0]["origin"][1]
        .as_array_mut()
        .unwrap()
        .pop();
    assert!(
        DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&short).unwrap()).is_err()
    );
    let mut long = wire.clone();
    long["descriptors"][0]["provenance"]["origins"][0]["origin"][1]
        .as_array_mut()
        .unwrap()
        .push(serde_json::Value::Null);
    assert!(
        DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&long).unwrap()).is_err()
    );
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][1] = 999.into();
    let bad_file = serde_json::to_vec(&wire).unwrap();
    assert!(DescriptorBundle::from_collector_protocol(&bad_file).is_err());
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][1] = 0.into();
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][4] = 999.into();
    let bad_item = serde_json::to_vec(&wire).unwrap();
    assert!(DescriptorBundle::from_collector_protocol(&bad_item).is_err());
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][4] = 0.into();
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][0] = 99.into();
    let bad_code = serde_json::to_vec(&wire).unwrap();
    assert!(DescriptorBundle::from_collector_protocol(&bad_code).is_err());
    wire["descriptors"][0]["provenance"]["origins"][0]["origin"][1][0] = 1.into();
    wire["protocol_version"] = 38.into();
    let error =
        DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&wire).unwrap()).unwrap_err();
    assert!(error.to_string().contains("unsupported collector protocol"));
    wire["protocol_version"] = collector::VERSION.into();
    wire["schema"] = (SchemaVersion::CURRENT.0 - 1).into();
    let error =
        DescriptorBundle::from_collector_protocol(&serde_json::to_vec(&wire).unwrap()).unwrap_err();
    assert!(error.to_string().contains("unsupported collector schema"));
}

#[test]
fn canonical_json_ignores_insertion_order() {
    assert_eq!(
        populated_bundle(false).to_canonical_json().unwrap(),
        populated_bundle(true).to_canonical_json().unwrap()
    );
}

#[test]
fn declaration_metadata_requires_exact_descriptor_coverage() {
    let bundle = populated_bundle(false);
    let declarations = || {
        bundle
            .descriptors
            .iter()
            .map(|descriptor| {
                DescriptorDeclaration::new(descriptor.id.clone(), RustVisibility::Inherited, None)
            })
            .collect::<Vec<_>>()
    };

    let mut missing = declarations();
    let missing_id = missing.pop().unwrap().id().clone();
    assert_eq!(
        DescriptorBundle::with_declarations(bundle.descriptors.clone(), missing),
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
        DescriptorBundle::with_declarations(bundle.descriptors.clone(), extra),
        Err(DescriptorDeclarationError::Extra(Box::new(extra_id)))
    );

    let mut duplicate = declarations();
    let duplicate_id = duplicate[0].id().clone();
    duplicate.push(duplicate[0].clone());
    assert_eq!(
        DescriptorBundle::with_declarations(bundle.descriptors, duplicate),
        Err(DescriptorDeclarationError::Duplicate(Box::new(
            duplicate_id
        )))
    );
}

#[test]
fn explicit_symbol_metadata_and_parser_provenance_must_agree() {
    let bundle = populated_bundle(false);
    let pinned_id = bundle.descriptors[0].id.clone();
    let mut declarations = bundle.declarations.clone();
    declarations[0] = DescriptorDeclaration::new(
        pinned_id.clone(),
        RustVisibility::Inherited,
        Some(ExplicitSymbol::new("api::Pinned").unwrap()),
    );
    assert_eq!(
        DescriptorBundle::with_declarations(bundle.descriptors.clone(), declarations),
        Err(DescriptorDeclarationError::MissingSymbolOrigin(Box::new(
            pinned_id.clone(),
        )))
    );

    let mut descriptors = bundle.descriptors;
    let primary_key = descriptors[0].provenance.primary_key().clone();
    let mut origins = descriptors[0].provenance.origins().to_vec();
    origins.push(DescriptorNodeOrigin::new(
        ProvenanceKey::new("stable_symbol", 0).unwrap(),
        origin(),
    ));
    descriptors[0].provenance = DescriptorProvenance::new(primary_key, origins).unwrap();
    assert_eq!(
        DescriptorBundle::with_declarations(descriptors, bundle.declarations),
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

    for path in ["", "crate::::private", "crate/private", "crate\\private"] {
        let wire = serde_json::json!({
            "visibility": "restricted",
            "path": path,
            "explicit_in": false
        });
        assert!(serde_json::from_value::<RustVisibility>(wire).is_err());
    }
}

#[test]
fn canonical_json_uses_payload_as_a_stable_tie_breaker() {
    let mut forward = populated_bundle(false);
    let mut alternate = forward.descriptors[0].clone();
    if let DescriptorPayload::Constructor(constructor) = &mut alternate.payload {
        constructor.syntax = Some("baz".into());
    }
    forward.descriptors.push(alternate.clone());

    let mut reverse = forward.clone();
    reverse.descriptors.reverse();
    assert_eq!(
        forward.to_canonical_json().unwrap(),
        reverse.to_canonical_json().unwrap()
    );
}

#[test]
fn canonical_json_orders_parser_keyed_origins_without_changing_primary() {
    let primary_key = ProvenanceKey::new("constructor_declaration", 0).unwrap();
    let nested_key = ProvenanceKey::new("constructor_field", 0).unwrap();
    let mut forward = populated_bundle(false);
    let descriptor = forward
        .descriptors
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

    let mut ordered = forward.clone();
    ordered
        .descriptors
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
    assert_eq!(
        forward.to_canonical_json().unwrap(),
        ordered.to_canonical_json().unwrap()
    );
    let descriptor = forward
        .descriptors
        .iter()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Constructor)
        .unwrap();
    assert_eq!(descriptor.provenance.primary_key(), &primary_key);
    assert_eq!(descriptor.origin(), descriptor.provenance.primary_origin());

    let round_trip: DescriptorBundle =
        serde_json::from_str(&forward.to_canonical_json().unwrap()).unwrap();
    let constructor = round_trip
        .descriptors
        .iter()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Constructor)
        .unwrap();
    assert!(
        constructor
            .provenance
            .origin_for(&ProvenanceKey::new("constructor_field", 0).unwrap())
            .is_some(),
        "an exact nested parser-keyed origin survives a round trip"
    );
}

#[test]
fn descriptor_provenance_rejects_empty_duplicate_and_missing_primary_tables() {
    let primary = ProvenanceKey::new("rule_declaration", 0).unwrap();
    let nested = ProvenanceKey::new("rule_right_path", 0).unwrap();
    assert!(DescriptorProvenance::new(primary.clone(), Vec::new()).is_err());
    assert!(
        DescriptorProvenance::new(
            primary.clone(),
            vec![DescriptorNodeOrigin::new(nested, origin())]
        )
        .is_err()
    );
    assert!(
        DescriptorProvenance::new(
            primary.clone(),
            vec![
                DescriptorNodeOrigin::new(primary.clone(), origin()),
                DescriptorNodeOrigin::new(primary, origin()),
            ]
        )
        .is_err()
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
    assert!(serde_json::from_value::<DescriptorProvenance>(value).is_err());

    let top_level =
        r#"{"protocol_version":20,"descriptors":[],"declarations":[],"unexpected":true}"#;
    assert!(serde_json::from_str::<DescriptorBundle>(top_level).is_err());
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
    let key = ProvenanceKey::new("rule_right_path", 7).unwrap();
    let json = serde_json::to_string(&key).unwrap();
    assert_eq!(serde_json::from_str::<ProvenanceKey>(&json).unwrap(), key);
    assert!(serde_json::from_str::<ProvenanceKey>(r#"{"role":"","ordinal":0}"#).is_err());
}

#[test]
fn empty_origin_stack_is_rejected_at_the_protocol_boundary() {
    assert!(serde_json::from_str::<OriginStack>("[]").is_err());
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
    assert!(serde_json::from_str::<OriginStack>(json).is_err());
}
