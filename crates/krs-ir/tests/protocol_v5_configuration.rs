//! Collector protocol v5 configuration and nested-origin contract tests.

use std::collections::BTreeMap;

use krs_ir::{
    BuiltinSort, ConfigurationCellDescriptor, ConfigurationDescriptor,
    ConfigurationDescriptorError, ConfigurationInitializerDescriptor,
    ConfigurationVariableDescriptor, Descriptor, DescriptorBundle, DescriptorNodeOrigin,
    DescriptorPayload, DescriptorProvenance, DescriptorReference, ItemKind, OriginFrame,
    OriginStack, PackageId, ProvenanceKey, RangedOriginKind, Sha256Digest, SourceFileId,
    SourceRange, StableItemId, TransformationOriginKind,
};

fn package() -> PackageId {
    PackageId::new("ORG-EXAMPLE-SMOKE", "smoke-semantics", "0.1.0", "workspace").unwrap()
}

fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package(), [module], name, kind, "").unwrap()
}

fn key(role: &str, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal).unwrap()
}

fn origin(path: &str, start: u32, item: &StableItemId, label: &str) -> OriginStack {
    let file = SourceFileId::new(
        package(),
        path,
        Sha256Digest::new("abcdef0123456789".repeat(4)).unwrap(),
    )
    .unwrap();
    let authored = SourceRange::new(file.clone(), start, start + 3).unwrap();
    let invocation = SourceRange::new(file, start.saturating_sub(1), start + 4).unwrap();
    let mut stack = OriginStack::authored(authored);
    stack.push(OriginFrame::Ranged {
        kind: RangedOriginKind::MacroInvocation,
        range: invocation,
        item: Some(item.clone()),
        label: Some(label.into()),
    });
    stack.push(OriginFrame::Transformation {
        kind: TransformationOriginKind::GeneratedDescriptor,
        item: Some(item.clone()),
        label: Some(label.into()),
    });
    stack
}

#[allow(clippy::too_many_lines)]
fn populated_descriptor(reverse_sets: bool) -> Descriptor {
    let configuration_id = item("machine", "Machine", ItemKind::Configuration);
    let k_item = item("syntax", "KItem", ItemKind::Sort);
    let pair_id = item("syntax", "Pair", ItemKind::Constructor);
    let foo_id = item("syntax", "Foo", ItemKind::Constructor);
    let bar_id = item("syntax", "Bar", ItemKind::Constructor);
    let variable_key = key("configuration_variable_type", 0);
    let pair_key = key("initializer_term_path", 0);
    let foo_key = key("initializer_term_path", 1);
    let bar_key = key("initializer_term_path", 2);
    let mut references = vec![
        DescriptorReference::new(pair_key.clone(), pair_id),
        DescriptorReference::new(foo_key.clone(), foo_id),
        DescriptorReference::new(bar_key.clone(), bar_id),
    ];
    let primary_key = key("configuration_declaration", 0);
    let mut origins = vec![
        DescriptorNodeOrigin::new(
            primary_key.clone(),
            origin("src/configuration.rs", 5, &configuration_id, "configuration"),
        ),
        DescriptorNodeOrigin::new(
            key("configuration_root", 0),
            origin("src/configuration.rs", 12, &configuration_id, "configuration"),
        ),
        DescriptorNodeOrigin::new(
            key("configuration_field", 0),
            origin(
                "src/configuration.rs",
                16,
                &configuration_id,
                "configuration",
            ),
        ),
        DescriptorNodeOrigin::new(
            key("configuration_cell_wrapper", 0),
            origin(
                "src/configuration.rs",
                18,
                &configuration_id,
                "configuration",
            ),
        ),
        DescriptorNodeOrigin::new(
            key("configuration_cell_content", 0),
            origin(
                "src/configuration.rs",
                20,
                &configuration_id,
                "configuration",
            ),
        ),
        DescriptorNodeOrigin::new(
            key("initializer_declaration", 0),
            origin("src/initializer.rs", 21, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            key("initializer_result_type", 0),
            origin("src/initializer.rs", 24, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            key("configuration_variable", 0),
            origin("src/initializer.rs", 26, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            key("configuration_variable_name", 0),
            origin("src/initializer.rs", 27, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            variable_key.clone(),
            origin("src/initializer.rs", 28, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            key("initializer_body", 0),
            origin("src/initializer.rs", 32, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            key("initializer_field", 0),
            origin("src/initializer.rs", 35, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            key("initializer_cell_constructor", 0),
            origin("src/initializer.rs", 37, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            key("initializer_term", 0),
            origin("src/initializer.rs", 40, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            pair_key,
            origin("src/initializer.rs", 44, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            foo_key,
            origin("src/initializer.rs", 50, &configuration_id, "initializer"),
        ),
        DescriptorNodeOrigin::new(
            bar_key,
            origin("src/initializer.rs", 56, &configuration_id, "initializer"),
        ),
    ];
    if reverse_sets {
        references.reverse();
        origins.reverse();
    }
    Descriptor {
        id: configuration_id,
        cfg: BTreeMap::new(),
        provenance: DescriptorProvenance::new(primary_key, origins).unwrap(),
        payload: DescriptorPayload::Configuration(ConfigurationDescriptor {
            root: "machine".into(),
            cell: ConfigurationCellDescriptor {
                name: "k".into(),
                content_sort: BuiltinSort::KSequence,
            },
            main_variable: Some(ConfigurationVariableDescriptor {
                binding: "program".into(),
                external_name: "PGM".into(),
                sort: DescriptorReference::new(variable_key, k_item),
            }),
            initializer: ConfigurationInitializerDescriptor {
                name: "init".into(),
                term: "model :: Pair (model :: Foo, model :: Bar)".into(),
                references,
            },
        }),
    }
}

fn populated_bundle(reverse_sets: bool) -> DescriptorBundle {
    DescriptorBundle::new(vec![populated_descriptor(reverse_sets)])
}

fn configuration(descriptor: &Descriptor) -> &ConfigurationDescriptor {
    let DescriptorPayload::Configuration(configuration) = &descriptor.payload else {
        panic!("expected configuration payload")
    };
    configuration
}

fn configuration_mut(descriptor: &mut Descriptor) -> &mut ConfigurationDescriptor {
    let DescriptorPayload::Configuration(configuration) = &mut descriptor.payload else {
        panic!("expected configuration payload")
    };
    configuration
}

#[test]
fn protocol_v5_populated_configuration_matches_golden() {
    assert_eq!(
        populated_bundle(false).to_canonical_json().unwrap(),
        include_str!("golden/configuration_v5.json")
    );
}

#[test]
fn fixed_configuration_reconstructs_m2_semantic_inputs() {
    let descriptor = populated_descriptor(false);
    descriptor.validate_configuration_contract().unwrap();
    let configuration = configuration(&descriptor);
    assert_eq!(descriptor.id.item_kind(), ItemKind::Configuration);
    assert_eq!(configuration.root, "machine");
    assert_eq!(configuration.cell.name, "k");
    assert_eq!(configuration.cell.content_sort, BuiltinSort::KSequence);
    let variable = configuration.main_variable.as_ref().unwrap();
    assert_eq!(variable.binding, "program");
    assert_eq!(variable.external_name, "PGM");
    assert_eq!(variable.sort.target.item_kind(), ItemKind::Sort);
    assert_eq!(configuration.initializer.name, "init");
    assert_eq!(configuration.initializer.references.len(), 3);
    let declaration_origin = descriptor
        .provenance
        .origin_for(&key("configuration_declaration", 0))
        .unwrap();
    let initializer_origin = descriptor
        .provenance
        .origin_for(&key("initializer_declaration", 0))
        .unwrap();
    assert_ne!(
        declaration_origin.frames()[0],
        initializer_origin.frames()[0],
        "the struct and associated initializer retain separate invocations"
    );
}

#[test]
fn main_configuration_variable_is_optional_but_singular() {
    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor).main_variable = None;
    assert!(descriptor.validate_configuration_contract().is_ok());
    assert!(configuration(&descriptor).main_variable.is_none());
}

#[test]
fn fixed_shape_rejects_blank_or_non_m2_values() {
    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor).root = " ".into();
    assert_eq!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::EmptyRoot)
    );

    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor).cell.name = "computation".into();
    assert!(matches!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::InvalidCellName(_))
    ));

    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor).initializer.name = "default".into();
    assert!(matches!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::InvalidInitializerName(_))
    ));

    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor).initializer.term.clear();
    assert_eq!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::EmptyInitializerTerm)
    );

    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor)
        .main_variable
        .as_mut()
        .unwrap()
        .binding = " ".into();
    assert_eq!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::EmptyVariableBinding)
    );

    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor)
        .main_variable
        .as_mut()
        .unwrap()
        .external_name
        .clear();
    assert_eq!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::EmptyVariableName)
    );
}

#[test]
fn semantic_reference_roles_and_target_kinds_are_checked() {
    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor)
        .main_variable
        .as_mut()
        .unwrap()
        .sort
        .key = key("initializer_result_type", 0);
    assert!(matches!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::InvalidVariableSortKey(_))
    ));

    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor).initializer.references[0].key =
        key("initializer_cell_constructor", 0);
    assert!(matches!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::InvalidInitializerReferenceKey(_))
    ));

    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor)
        .main_variable
        .as_mut()
        .unwrap()
        .sort
        .target = item("syntax", "Foo", ItemKind::Constructor);
    assert!(matches!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::ReferenceKindMismatch {
            expected: ItemKind::Sort,
            ..
        })
    ));

    let mut descriptor = populated_descriptor(false);
    configuration_mut(&mut descriptor).initializer.references[0].target =
        item("syntax", "Value", ItemKind::Sort);
    assert!(matches!(
        descriptor.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::ReferenceKindMismatch {
            expected: ItemKind::Constructor,
            ..
        })
    ));
}

#[test]
fn duplicate_and_missing_parser_joins_are_rejected() {
    let mut duplicate = populated_descriptor(false);
    let repeated = configuration(&duplicate).initializer.references[0]
        .key
        .clone();
    configuration_mut(&mut duplicate).initializer.references[1].key = repeated;
    assert!(matches!(
        duplicate.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::DuplicateReferenceKey(_))
    ));

    let mut missing = populated_descriptor(false);
    let primary = missing.provenance.primary_key().clone();
    let omitted = key("initializer_term_path", 0);
    let origins = missing
        .provenance
        .origins()
        .iter()
        .filter(|node| node.key != omitted)
        .cloned()
        .collect();
    missing.provenance = DescriptorProvenance::new(primary, origins).unwrap();
    assert_eq!(
        missing.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::MissingInitializerReferenceOrigin(
            omitted
        ))
    );

    let encoded = serde_json::to_string(&DescriptorBundle::new(vec![missing])).unwrap();
    assert!(serde_json::from_str::<DescriptorBundle>(&encoded).is_err());
}

#[test]
fn canonicalization_reorders_sets_but_not_term_order() {
    assert_eq!(
        populated_bundle(false).to_canonical_json().unwrap(),
        populated_bundle(true).to_canonical_json().unwrap()
    );

    let mut reordered_term = populated_bundle(false);
    configuration_mut(&mut reordered_term.descriptors[0]).initializer.term =
        "model :: Pair (model :: Bar, model :: Foo)".into();
    assert_ne!(
        populated_bundle(false).to_canonical_json().unwrap(),
        reordered_term.to_canonical_json().unwrap()
    );
}

#[test]
fn stable_configuration_has_no_host_pairing_or_wrapper_values() {
    let json = populated_bundle(false).to_canonical_json().unwrap();
    for forbidden in [
        "TypeId",
        "owner_type",
        "KCell",
        "KCell::new",
        "Self",
        "/home/",
    ] {
        assert!(!json.contains(forbidden), "leaked `{forbidden}` into v5");
    }
    assert!(json.contains("\"content_sort\": \"k_sequence\""));
    assert!(json.contains("\"item_kind\": \"configuration\""));
    assert!(!json.contains("\"item_kind\": \"initializer\""));
}

#[test]
fn configuration_deserialization_rejects_unknown_fields_and_wrong_outer_kind() {
    let descriptor = populated_descriptor(false);
    let mut payload = serde_json::to_value(configuration(&descriptor)).unwrap();
    payload
        .as_object_mut()
        .unwrap()
        .insert("unexpected".into(), serde_json::Value::Bool(true));
    assert!(serde_json::from_value::<ConfigurationDescriptor>(payload).is_err());

    let mut wrong_kind = populated_descriptor(false);
    wrong_kind.id = item("machine", "Machine", ItemKind::Rule);
    assert!(matches!(
        wrong_kind.validate_configuration_contract(),
        Err(ConfigurationDescriptorError::ConfigurationItemKindMismatch(
            ItemKind::Rule
        ))
    ));
}
