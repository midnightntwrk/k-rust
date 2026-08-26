//! Golden protocol and serialization-boundary tests.

use std::collections::BTreeMap;

use krs_ir::{
    ConstructorDescriptor, ConstructorFieldDescriptor, Descriptor, DescriptorBundle,
    DescriptorDeclaration, DescriptorDeclarationError, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorProvenance, DescriptorReference, DescriptorSortRef, ExplicitSymbol, ItemKind,
    OriginFrame, OriginStack, PackageId, ProvenanceKey, RuleDescriptor, RuleParameterDescriptor,
    RustVisibility, SentenceKind, Sha256Digest, SortDescriptor, SourceFileId, SourceRange,
    StableItemId, TransformationOriginKind,
};
use serde::Serialize;
use static_assertions::assert_not_impl_any;

fn package() -> PackageId {
    PackageId::new("ORG-EXAMPLE-SMOKE", "smoke-semantics", "0.1.0", "workspace").unwrap()
}

fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package(), [module], name, kind, "").unwrap()
}

fn origin() -> OriginStack {
    let file = SourceFileId::new(
        package(),
        "src/lib.rs",
        Sha256Digest::new("0123456789abcdef".repeat(4)).unwrap(),
    )
    .unwrap();
    OriginStack::authored(SourceRange::new(file, 0, 3).unwrap())
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
    let rewrite = item("rules", "foo_to_bar", ItemKind::Rule);

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
    let rule = descriptor(
        rewrite,
        DescriptorPayload::Rule(RuleDescriptor {
            sentence_kind: SentenceKind::Transition,
            parameters: vec![RuleParameterDescriptor {
                bindings: vec!["x".into()],
                sort: value.clone(),
                pattern: "Foo { value: x }".into(),
            }],
            result_sort: value,
            references: vec![DescriptorReference::new(
                ProvenanceKey::new("rule_right_path", 0).unwrap(),
                bar_constructor,
            )],
            lhs: "Foo { value: x }".into(),
            rhs: "Bar { value: x }".into(),
        }),
    );

    let mut descriptors = vec![rule, sort, constructor];
    if reverse {
        descriptors.reverse();
    }
    DescriptorBundle::new(descriptors)
}

#[test]
fn empty_bundle_matches_golden() {
    assert_eq!(
        DescriptorBundle::empty().to_canonical_json().unwrap(),
        include_str!("golden/empty_bundle.json")
    );
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
    let actual: serde_json::Value =
        serde_json::from_str(&populated_bundle(false).to_canonical_json().unwrap()).unwrap();
    let expected: serde_json::Value =
        serde_json::from_str(include_str!("golden/sort_constructor_rule.json")).unwrap();
    assert_eq!(actual, expected);
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
    if let DescriptorPayload::Rule(rule) = &mut alternate.payload {
        rule.rhs = "Baz { value: x }".into();
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
fn canonical_json_orders_parser_keyed_rule_references() {
    let left = DescriptorReference::new(
        ProvenanceKey::new("rule_left_path", 0).unwrap(),
        item("syntax", "Foo", ItemKind::Constructor),
    );
    let right = DescriptorReference::new(
        ProvenanceKey::new("rule_right_path", 0).unwrap(),
        item("syntax", "Bar", ItemKind::Constructor),
    );
    let mut forward = populated_bundle(false);
    let rule = forward
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::Rule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.references = vec![right.clone(), left.clone()];

    let mut ordered = forward.clone();
    let rule = ordered
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::Rule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.references = vec![left, right];
    assert_eq!(
        forward.to_canonical_json().unwrap(),
        ordered.to_canonical_json().unwrap()
    );
}

#[test]
fn canonical_json_orders_parser_keyed_origins_without_changing_primary() {
    let primary_key = ProvenanceKey::new("rule_declaration", 0).unwrap();
    let nested_key = ProvenanceKey::new("rule_right_path", 0).unwrap();
    let mut forward = populated_bundle(false);
    let descriptor = forward
        .descriptors
        .iter_mut()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Rule)
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
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Rule)
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
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Rule)
        .unwrap();
    assert_eq!(descriptor.provenance.primary_key(), &primary_key);
    assert_eq!(descriptor.origin(), descriptor.provenance.primary_origin());

    let round_trip: DescriptorBundle =
        serde_json::from_str(&forward.to_canonical_json().unwrap()).unwrap();
    let rule = round_trip
        .descriptors
        .iter()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Rule)
        .unwrap();
    assert!(
        rule.provenance
            .origin_for(&ProvenanceKey::new("rule_right_path", 0).unwrap())
            .is_some(),
        "an exact existing-rule term origin survives protocol v5"
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
        r#"{"protocol_version":17,"descriptors":[],"declarations":[],"unexpected":true}"#;
    assert!(serde_json::from_str::<DescriptorBundle>(top_level).is_err());
}

#[test]
fn rule_reference_keys_must_be_unique() {
    let reference = DescriptorReference::new(
        ProvenanceKey::new("rule_left_path", 0).unwrap(),
        item("syntax", "Foo", ItemKind::Constructor),
    );
    let mut bundle = populated_bundle(false);
    let rule = bundle
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::Rule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.references = vec![reference.clone(), reference];
    assert!(rule.validate_reference_keys().is_err());
}

#[test]
fn zero_bindings_are_legal() {
    let parameter = RuleParameterDescriptor {
        bindings: Vec::new(),
        sort: item("syntax", "Value", ItemKind::Sort),
        pattern: "True".into(),
    };
    assert!(parameter.validate_bindings().is_ok());
}

#[test]
fn binding_preorder_is_semantic_and_never_canonicalized() {
    let mut forward = populated_bundle(false);
    let rule = forward
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::Rule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.parameters[0].bindings = vec!["numerator".into(), "denominator".into()];
    assert!(rule.validate_bindings().is_ok());

    let mut reversed = forward.clone();
    let rule = reversed
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::Rule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.parameters[0].bindings.reverse();
    assert_ne!(
        forward.to_canonical_json().unwrap(),
        reversed.to_canonical_json().unwrap()
    );
}

#[test]
fn blank_and_duplicate_bindings_are_rejected() {
    let mut bundle = populated_bundle(false);
    let rule = bundle
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::Rule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.parameters[0].bindings = vec!["numerator".into(), " ".into()];
    assert!(rule.validate_bindings().is_err());
    rule.parameters[0].bindings = vec!["numerator".into(), "numerator".into()];
    assert!(rule.validate_bindings().is_err());
}

#[test]
fn host_only_values_cannot_implement_serialization() {
    assert_not_impl_any!(krs_ir::HostTypeKey: Serialize);
    assert_not_impl_any!(krs_ir::HostDescriptor: Serialize);
    assert_not_impl_any!(krs_ir::HostSourceAnchor: Serialize);
    assert_not_impl_any!(krs_ir::HostProvenance: Serialize);
    assert_not_impl_any!(krs_ir::HostPackageKey: Serialize);
    assert_not_impl_any!(krs_ir::HostItemId: Serialize);
    assert_not_impl_any!(krs_ir::HostDescriptorReference: Serialize);
    assert_not_impl_any!(krs_ir::HostConstructorFieldDescriptor: Serialize);
    assert_not_impl_any!(krs_ir::HostConfigurationDescriptor: Serialize);
    assert_not_impl_any!(krs_ir::HostConfigurationInitializerDescriptor: Serialize);
    assert_not_impl_any!(krs_ir::HostConfigurationVariableDescriptor: Serialize);
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
