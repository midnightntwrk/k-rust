//! Typed collector protocol-v6 contract tests.

use std::any::TypeId;
use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinOperation, BuiltinSort, Descriptor, DescriptorApplicationHeadClass,
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorAssociativitySentence,
    DescriptorBundle, DescriptorFieldReference, DescriptorFormatFragment, DescriptorGroupReference,
    DescriptorLexicalPrecedence, DescriptorLiteral, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorPrecedenceChain, DescriptorProduction, DescriptorProductionAttribute,
    DescriptorProductionItem, DescriptorProductionOwner, DescriptorProvenance,
    DescriptorRuleCondition, DescriptorRuleLabel, DescriptorSortRef, DescriptorSortReference,
    DescriptorTerm, DescriptorTermArgument, FormatFragment, GrammarDescriptor, GroupAssociativity,
    HostApplicationIdentity, HostApplicationTarget, HostBuiltinOperationRegistration,
    HostBuiltinRegistry, HostBuiltinRegistryError, HostBuiltinSortRegistration,
    HostDeclarationIdentity, HostEnumVariantKey, HostEnumVariantReference,
    HostEnumVariantReferenceError, HostMapOperationRegistration, HostTypeKey, HostTypeReference,
    ItemKind, MapOperation, OriginStack, PackageId, ProductionFieldId, ProductionGroupId,
    ProtocolV6ShapeError, ProvenanceKey, SentenceKind, Sha256Digest, SourceFileId, SourceRange,
    StableItemId, StrictnessKind, StructuredRuleDescriptor, enum_variant_disambiguator,
};

type IntAlias = u16;

#[allow(dead_code)]
struct Add;

type AddAlias = Add;

#[allow(dead_code, non_snake_case)]
enum Boolean {
    True,
    False,
}

#[allow(dead_code)]
struct TrueVariantMarker;

#[allow(dead_code)]
struct FalseVariantMarker;

#[allow(non_snake_case)]
impl Boolean {
    fn __krs_variant_key_True() -> TypeId {
        TypeId::of::<TrueVariantMarker>()
    }

    fn __krs_variant_key_False() -> TypeId {
        TypeId::of::<FalseVariantMarker>()
    }
}

type BooleanTypeAlias = Boolean;
use Boolean as BooleanUseAlias;
use Boolean::False as StandaloneFalse;

mod boolean_api {
    pub(super) use super::Boolean as ReexportAlias;
}

#[allow(dead_code, non_snake_case)]
enum OtherBoolean {
    False,
}

#[allow(dead_code)]
struct OtherFalseVariantMarker;

#[allow(non_snake_case)]
impl OtherBoolean {
    fn __krs_variant_key_False() -> TypeId {
        TypeId::of::<OtherFalseVariantMarker>()
    }
}

fn package() -> PackageId {
    PackageId::new("IMP", "imp-semantics", "0.1.0", "workspace").unwrap()
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package(), ["expr"], name, kind, "").unwrap()
}

fn key(role: &str, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal).unwrap()
}

fn origin(start: u32) -> OriginStack {
    let file = SourceFileId::new(
        package(),
        "src/expr.rs",
        Sha256Digest::new("1234567890abcdef".repeat(4)).unwrap(),
    )
    .unwrap();
    OriginStack::authored(SourceRange::new(file, start, start + 1).unwrap())
}

fn provenance(primary: ProvenanceKey, keys: &[ProvenanceKey]) -> DescriptorProvenance {
    let mut all = vec![primary.clone()];
    all.extend_from_slice(keys);
    all.sort();
    all.dedup();
    DescriptorProvenance::new(
        primary,
        all.into_iter()
            .enumerate()
            .map(|(index, key)| {
                DescriptorNodeOrigin::new(key, origin(u32::try_from(index).unwrap()))
            })
            .collect(),
    )
    .unwrap()
}

fn declared_sort(role: &str, ordinal: u32, id: StableItemId) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(role, ordinal),
        sort: DescriptorSortRef::Declared(id),
    }
}

#[allow(clippy::too_many_lines)]
fn expression_descriptors() -> Vec<Descriptor> {
    let expr = item("Expr", ItemKind::Sort);
    let value = item("Value", ItemKind::Sort);
    let add = item("Add", ItemKind::Constructor);
    let grammar_id = item("__grammar_Add", ItemKind::Grammar);
    let rule_id = item("add_zero", ItemKind::Rule);

    let grammar_primary = key("constructor_declaration", 0);
    let grammar_keys = [
        key("constructor_sort", 0),
        key("constructor_syntax", 0),
        key("constructor_syntax_item", 0),
        key("constructor_syntax_item", 1),
        key("constructor_syntax_item", 2),
        key("constructor_syntax_field_reference", 0),
        key("constructor_syntax_field_reference", 1),
        key("constructor_field_sort", 0),
        key("constructor_field_sort", 1),
        key("constructor_field_declaration", 0),
        key("constructor_field_declaration", 1),
        key("constructor_group", 0),
        key("constructor_avoid", 0),
        key("constructor_format", 0),
        key("constructor_format_fragment", 0),
        key("constructor_format_fragment", 1),
        key("constructor_format_fragment", 2),
        key("constructor_documentation", 0),
        key("constructor_documentation", 1),
        key("strictness_declaration", 0),
        key("strictness_field_reference", 0),
        key("strictness_field_reference", 1),
        key("strictness_result_sort", 0),
    ];
    let grammar = Descriptor {
        id: grammar_id,
        cfg: BTreeMap::new(),
        provenance: provenance(grammar_primary.clone(), &grammar_keys),
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Production(
            DescriptorProduction {
                key: grammar_primary.clone(),
                template_key: Some(key("constructor_syntax", 0)),
                owner: DescriptorProductionOwner::Constructor {
                    constructor: DescriptorApplicationReference {
                        key: grammar_primary,
                        application: DescriptorApplicationRef::Declared(add.clone()),
                    },
                },
                result_sort: declared_sort("constructor_sort", 0, expr.clone()),
                items: vec![
                    DescriptorProductionItem::NonTerminal {
                        key: key("constructor_syntax_item", 0),
                        field_key: key("constructor_syntax_field_reference", 0),
                        declaration_key: Some(key("constructor_field_declaration", 0)),
                        field: ProductionFieldId::new("lhs").unwrap(),
                        sort: Box::new(declared_sort("constructor_field_sort", 0, expr.clone())),
                    },
                    DescriptorProductionItem::Terminal {
                        key: key("constructor_syntax_item", 1),
                        text: "+".into(),
                    },
                    DescriptorProductionItem::NonTerminal {
                        key: key("constructor_syntax_item", 2),
                        field_key: key("constructor_syntax_field_reference", 1),
                        declaration_key: Some(key("constructor_field_declaration", 1)),
                        field: ProductionFieldId::new("rhs").unwrap(),
                        sort: Box::new(declared_sort("constructor_field_sort", 1, expr.clone())),
                    },
                ],
                attributes: vec![
                    DescriptorProductionAttribute::Documentation {
                        key: key("constructor_documentation", 0),
                        text: "Adds two values.".into(),
                    },
                    DescriptorProductionAttribute::Documentation {
                        key: key("constructor_documentation", 1),
                        text: "Evaluation is sequential.".into(),
                    },
                    DescriptorProductionAttribute::Group {
                        reference: DescriptorGroupReference {
                            key: key("constructor_group", 0),
                            group: ProductionGroupId::new("additive").unwrap(),
                        },
                    },
                    DescriptorProductionAttribute::Avoid {
                        key: key("constructor_avoid", 0),
                    },
                    DescriptorProductionAttribute::Format {
                        key: key("constructor_format", 0),
                        fragments: vec![
                            DescriptorFormatFragment {
                                key: key("constructor_format_fragment", 0),
                                fragment: FormatFragment::Item(1),
                            },
                            DescriptorFormatFragment {
                                key: key("constructor_format_fragment", 1),
                                fragment: FormatFragment::Literal(" ".into()),
                            },
                            DescriptorFormatFragment {
                                key: key("constructor_format_fragment", 2),
                                fragment: FormatFragment::Item(3),
                            },
                        ],
                    },
                    DescriptorProductionAttribute::Strictness {
                        key: key("strictness_declaration", 0),
                        kind: StrictnessKind::SeqStrict,
                        using: None,
                        fields: vec![
                            DescriptorFieldReference {
                                key: key("strictness_field_reference", 0),
                                field: ProductionFieldId::new("lhs").unwrap(),
                            },
                            DescriptorFieldReference {
                                key: key("strictness_field_reference", 1),
                                field: ProductionFieldId::new("rhs").unwrap(),
                            },
                        ],
                        result_sort: Box::new(declared_sort("strictness_result_sort", 0, value)),
                    },
                ],
            },
        ))),
    };

    let rule_primary = key("rule_declaration", 0);
    let rule_keys = [
        key("rule_type", 0),
        key("rule_result_type", 0),
        key("rule_pattern", 0),
        key("rule_result", 0),
        key("rule_left_path", 0),
        key("rule_left_path", 1),
        key("rule_right_path", 0),
        key("rule_left_application_head", 0),
        key("rule_left_record_field_name", 0),
        key("rule_left_record_field_name", 1),
        key("rule_left_reference", 0),
        key("rule_left_wildcard", 0),
        key("rule_right_reference", 0),
    ];
    let variable = || DescriptorTerm::Variable {
        key: key("rule_left_reference", 0),
        path_key: key("rule_left_path", 1),
        name: "x".into(),
    };
    let rule = Descriptor {
        id: rule_id,
        cfg: BTreeMap::new(),
        provenance: provenance(rule_primary, &rule_keys),
        payload: DescriptorPayload::StructuredRule(Box::new(StructuredRuleDescriptor {
            sentence_kind: SentenceKind::Transition,
            label: None,
            requires: None,
            priority: None,
            simplification: None,
            pattern_key: key("rule_pattern", 0),
            result_key: key("rule_result", 0),
            subject_sort: declared_sort("rule_type", 0, expr.clone()),
            result_sort: declared_sort("rule_result_type", 0, expr),
            bindings: vec!["x".into()],
            subject: DescriptorTerm::Application {
                head_class: DescriptorApplicationHeadClass::Applied,
                reference: DescriptorApplicationReference {
                    key: key("rule_left_application_head", 0),
                    application: DescriptorApplicationRef::Declared(add),
                },
                path_key: key("rule_left_path", 0),
                arguments: vec![
                    DescriptorTermArgument::Named {
                        key: key("rule_left_record_field_name", 0),
                        field: ProductionFieldId::new("rhs").unwrap(),
                        value: Box::new(DescriptorTerm::Wildcard {
                            key: key("rule_left_wildcard", 0),
                        }),
                    },
                    DescriptorTermArgument::Named {
                        key: key("rule_left_record_field_name", 1),
                        field: ProductionFieldId::new("lhs").unwrap(),
                        value: Box::new(variable()),
                    },
                ],
            },
            result: DescriptorTerm::Variable {
                key: key("rule_right_reference", 0),
                path_key: key("rule_right_path", 0),
                name: "x".into(),
            },
        })),
    };
    vec![grammar, rule]
}

#[test]
fn expression_grammar_and_rule_round_trip_deterministically() {
    let descriptors = expression_descriptors();
    for descriptor in &descriptors {
        descriptor.validate_v6_contract().unwrap();
    }
    let forward = DescriptorBundle::new(descriptors.clone())
        .to_canonical_json()
        .unwrap();
    let reverse = DescriptorBundle::new(descriptors.into_iter().rev().collect())
        .to_canonical_json()
        .unwrap();
    assert_eq!(forward, reverse);
    assert!(forward.contains("\"protocol_version\": 17"));
    assert!(forward.contains("\"attribute_kind\": \"documentation\""));
    assert!(forward.contains("Adds two values."));
    assert!(forward.contains("\"structured_rule\""));
    assert!(forward.contains("\"grammar_kind\": \"production\""));
    assert!(!forward.contains("TypeId"));
    assert!(!forward.contains("_+Int_"));
    let decoded: DescriptorBundle = serde_json::from_str(&forward).unwrap();
    assert_eq!(decoded.protocol_version().0, 17);
}

#[test]
fn explicit_rule_label_requires_exact_provenance_and_a_portable_name() {
    let mut descriptors = expression_descriptors();
    let descriptor = &mut descriptors[1];
    let label_key = key("rule_label", 0);
    let primary = descriptor.provenance.primary_key().clone();
    let mut origins = descriptor.provenance.origins().to_vec();
    origins.push(DescriptorNodeOrigin::new(label_key.clone(), origin(77)));
    descriptor.provenance = DescriptorProvenance::new(primary, origins).unwrap();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!()
    };
    rule.label = Some(DescriptorRuleLabel {
        key: label_key.clone(),
        name: "if-true".into(),
    });

    descriptor.validate_v6_contract().unwrap();
    assert_eq!(
        descriptor.provenance.origin_for(&label_key),
        Some(&origin(77))
    );

    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!()
    };
    rule.label.as_mut().unwrap().name = "if true".into();
    assert!(matches!(
        descriptor.validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidTerm(
            "invalid explicit rule label"
        ))
    ));
}

#[test]
#[allow(clippy::too_many_lines)]
fn protocol_v11_structured_requires_has_closed_exact_provenance_and_pre_bindings() {
    let mut descriptors = expression_descriptors();
    let descriptor = &mut descriptors[1];
    let condition_keys = [
        key("rule_requires", 0),
        key("rule_requires_path", 0),
        key("rule_requires_path", 1),
        key("rule_requires_application_head", 0),
        key("rule_requires_reference", 0),
        key("rule_requires_literal", 0),
    ];
    let primary = descriptor.provenance.primary_key().clone();
    let mut origins = descriptor.provenance.origins().to_vec();
    origins.extend(
        condition_keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(ordinal, key)| {
                DescriptorNodeOrigin::new(
                    key,
                    origin(100 + u32::try_from(ordinal).expect("six condition keys fit u32")),
                )
            }),
    );
    descriptor.provenance = DescriptorProvenance::new(primary, origins).unwrap();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!()
    };
    rule.requires = Some(DescriptorRuleCondition {
        key: key("rule_requires", 0),
        term: DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key("rule_requires_application_head", 0),
                application: DescriptorApplicationRef::Builtin(BuiltinOperation::IntGreater),
            },
            path_key: key("rule_requires_path", 0),
            arguments: vec![
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Variable {
                        key: key("rule_requires_reference", 0),
                        path_key: key("rule_requires_path", 1),
                        name: "x".into(),
                    }),
                },
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Literal {
                        key: key("rule_requires_literal", 0),
                        literal: DescriptorLiteral::Int("0".into()),
                    }),
                },
            ],
        },
    });

    descriptor.validate_v6_contract().unwrap();
    for condition_key in condition_keys {
        assert!(descriptor.provenance.origin_for(&condition_key).is_some());
    }

    let mut wrong_path = descriptor.clone();
    let DescriptorPayload::StructuredRule(rule) = &mut wrong_path.payload else {
        unreachable!()
    };
    let DescriptorTerm::Application { path_key, .. } = &mut rule.requires.as_mut().unwrap().term
    else {
        unreachable!()
    };
    *path_key = key("rule_requires_path", 1);
    assert!(matches!(
        wrong_path.validate_v6_contract(),
        Err(ProtocolV6ShapeError::UnexpectedProvenance { .. })
    ));

    let mut unbound = descriptor.clone();
    let DescriptorPayload::StructuredRule(rule) = &mut unbound.payload else {
        unreachable!()
    };
    let DescriptorTerm::Application { arguments, .. } = &mut rule.requires.as_mut().unwrap().term
    else {
        unreachable!()
    };
    let DescriptorTermArgument::Positional { value } = &mut arguments[0] else {
        unreachable!()
    };
    let DescriptorTerm::Variable { name, .. } = value.as_mut() else {
        unreachable!()
    };
    *name = "post_only".into();
    assert!(matches!(
        unbound.validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidBinding(name)) if name == "post_only"
    ));

    let mut post_only = descriptor.clone();
    let DescriptorPayload::StructuredRule(rule) = &mut post_only.payload else {
        unreachable!()
    };
    let DescriptorTerm::Variable { name, .. } = &mut rule.result else {
        unreachable!()
    };
    *name = "post_only".into();
    let DescriptorTerm::Application { arguments, .. } = &mut rule.requires.as_mut().unwrap().term
    else {
        unreachable!()
    };
    let DescriptorTermArgument::Positional { value } = &mut arguments[0] else {
        unreachable!()
    };
    let DescriptorTerm::Variable { name, .. } = value.as_mut() else {
        unreachable!()
    };
    *name = "post_only".into();
    assert!(matches!(
        post_only.validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidBinding(name)) if name == "post_only"
    ));
}

fn expression_production(descriptor: &mut Descriptor) -> &mut DescriptorProduction {
    let DescriptorPayload::Grammar(grammar) = &mut descriptor.payload else {
        panic!("expected grammar descriptor")
    };
    let GrammarDescriptor::Production(production) = grammar.as_mut() else {
        panic!("expected production grammar")
    };
    production
}

fn reorder_expression_fields(production: &mut DescriptorProduction) {
    production.items.swap(0, 2);
    let DescriptorProductionItem::NonTerminal {
        key,
        field_key,
        field,
        ..
    } = &mut production.items[0]
    else {
        panic!("expected first nonterminal")
    };
    *key = crate_key("constructor_syntax_item", 0);
    *field_key = crate_key("constructor_syntax_field_reference", 0);
    *field = ProductionFieldId::new("rhs").unwrap();

    let DescriptorProductionItem::NonTerminal {
        key,
        field_key,
        field,
        ..
    } = &mut production.items[2]
    else {
        panic!("expected second nonterminal")
    };
    *key = crate_key("constructor_syntax_item", 2);
    *field_key = crate_key("constructor_syntax_field_reference", 1);
    *field = ProductionFieldId::new("lhs").unwrap();
}

fn crate_key(role: &str, ordinal: u32) -> ProvenanceKey {
    key(role, ordinal)
}

#[test]
fn explicit_constructor_syntax_tracks_occurrence_and_declaration_ordinals_separately() {
    let mut descriptors = expression_descriptors();
    reorder_expression_fields(expression_production(&mut descriptors[0]));
    descriptors[0].validate_v6_contract().unwrap();

    let production = expression_production(&mut descriptors[0]);
    let DescriptorProductionItem::NonTerminal { field_key, .. } = &mut production.items[0] else {
        unreachable!()
    };
    *field_key = key("constructor_syntax_field_reference", 1);
    assert!(matches!(
        descriptors[0].validate_v6_contract(),
        Err(ProtocolV6ShapeError::UnexpectedProvenance { .. })
    ));

    let mut descriptors = expression_descriptors();
    reorder_expression_fields(expression_production(&mut descriptors[0]));
    let production = expression_production(&mut descriptors[0]);
    let DescriptorProductionItem::NonTerminal {
        declaration_key,
        sort,
        ..
    } = &mut production.items[2]
    else {
        unreachable!()
    };
    *declaration_key = Some(key("constructor_field_declaration", 1));
    sort.key = key("constructor_field_sort", 1);
    assert!(matches!(
        descriptors[0].validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidProduction(
            "constructor field declaration ordinals must be unique"
        ))
    ));
}

#[test]
fn bare_unit_constructor_is_an_application_with_reference_provenance() {
    let mut descriptors = expression_descriptors();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptors[1].payload else {
        unreachable!()
    };
    rule.result = DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::BareReference,
        reference: DescriptorApplicationReference {
            key: key("rule_right_reference", 0),
            application: DescriptorApplicationRef::Declared(item("False", ItemKind::Constructor)),
        },
        path_key: key("rule_right_path", 0),
        arguments: vec![],
    };
    descriptors[1].validate_v6_contract().unwrap();
    let json = DescriptorBundle::new(descriptors)
        .to_canonical_json()
        .unwrap();
    assert!(json.contains("\"head_class\": \"bare_reference\""));

    let mut descriptors = expression_descriptors();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptors[1].payload else {
        unreachable!()
    };
    rule.result = DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::BareReference,
        reference: DescriptorApplicationReference {
            key: key("rule_right_reference", 0),
            application: DescriptorApplicationRef::Declared(item("False", ItemKind::Constructor)),
        },
        path_key: key("rule_right_path", 0),
        arguments: vec![DescriptorTermArgument::Positional {
            value: Box::new(DescriptorTerm::Literal {
                key: key("rule_right_literal", 0),
                literal: DescriptorLiteral::Int("0".into()),
            }),
        }],
    };
    assert!(matches!(
        descriptors[1].validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidApplication(
            "a bare-reference constructor must have no arguments"
        ))
    ));
}

#[test]
fn builtin_references_are_typed_and_raw_labels_are_unrepresentable() {
    let reference = DescriptorApplicationReference {
        key: key("rule_right_application_head", 0),
        application: DescriptorApplicationRef::Builtin(BuiltinOperation::IntTDiv),
    };
    let json = serde_json::to_string(&reference).unwrap();
    assert!(json.contains("int_t_div"));
    assert!(!json.contains("_/Int_"));
    let sort = DescriptorSortReference {
        key: key("rule_result_type", 0),
        sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
    };
    assert!(sort.sort.validate().is_ok());
}

#[test]
fn ordinary_map_update_reference_has_a_closed_wire_shape() {
    let variable = |name: &str| DescriptorTerm::Variable {
        key: key("rule_right_reference", 0),
        path_key: key("rule_right_path", 0),
        name: name.to_owned(),
    };
    let application = DescriptorApplicationReference {
        key: key("rule_right_application_head", 0),
        application: DescriptorApplicationRef::Map(MapOperation::Update),
    };
    assert_eq!(
        serde_json::to_string(&application).unwrap(),
        r#"{"key":{"role":"rule_right_application_head","ordinal":0},"application":{"application_source":"map","application":"update"}}"#
    );
    let term = DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: application,
        path_key: key("rule_right_path", 0),
        arguments: ["map", "key", "value"]
            .into_iter()
            .map(|name| DescriptorTermArgument::Positional {
                value: Box::new(variable(name)),
            })
            .collect(),
    };
    let bindings = ["map", "key", "value"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    term.validate(|_| true, &bindings, &mut BTreeSet::new(), false)
        .unwrap();

    let mut wrong_arity = term.clone();
    let DescriptorTerm::Application { arguments, .. } = &mut wrong_arity else {
        unreachable!()
    };
    arguments.pop();
    assert!(matches!(
        wrong_arity.validate(|_| true, &bindings, &mut BTreeSet::default(), false),
        Err(ProtocolV6ShapeError::InvalidApplication(
            "map::update requires exactly three arguments"
        ))
    ));

    assert!(matches!(
        DescriptorApplicationRef::Map(MapOperation::Item).validate(),
        Err(ProtocolV6ShapeError::InvalidApplication(
            "structural-only Map operation used as an application head"
        ))
    ));
}

fn grammar_descriptor(
    id: StableItemId,
    primary: ProvenanceKey,
    keys: &[ProvenanceKey],
    grammar: GrammarDescriptor,
) -> Descriptor {
    Descriptor {
        id,
        cfg: BTreeMap::new(),
        provenance: provenance(primary, keys),
        payload: DescriptorPayload::Grammar(Box::new(grammar)),
    }
}

#[allow(clippy::too_many_lines)]
#[test]
fn token_bracket_subsort_precedence_and_associativity_are_complete() {
    let id_sort = item("Id", ItemKind::Sort);
    let expr_sort = item("Expr", ItemKind::Sort);
    let value_sort = item("Value", ItemKind::Sort);

    let token_primary = key("token_declaration", 0);
    let token = grammar_descriptor(
        item("__grammar_Id", ItemKind::Grammar),
        token_primary.clone(),
        &[key("token_regex", 0), key("token_lexical_precedence", 0)],
        GrammarDescriptor::Production(DescriptorProduction {
            key: token_primary.clone(),
            template_key: None,
            owner: DescriptorProductionOwner::TokenSort {
                sort: DescriptorSortReference {
                    key: token_primary.clone(),
                    sort: DescriptorSortRef::Declared(id_sort),
                },
            },
            result_sort: DescriptorSortReference {
                key: token_primary.clone(),
                sort: DescriptorSortRef::Declared(item("Id", ItemKind::Sort)),
            },
            items: vec![DescriptorProductionItem::RegexTerminal {
                key: key("token_regex", 0),
                precede_regex: None,
                regex: "[a-zA-Z][a-zA-Z0-9_]*".into(),
                follow_regex: None,
            }],
            attributes: vec![DescriptorProductionAttribute::Token {
                key: key("token_regex", 0),
                lexical_precedence: Some(DescriptorLexicalPrecedence {
                    key: key("token_lexical_precedence", 0),
                    value: 2,
                }),
            }],
        }),
    );

    let bracket_primary = key("bracket_declaration", 0);
    let bracket = grammar_descriptor(
        item("__grammar_Expr_bracket_0", ItemKind::Grammar),
        bracket_primary.clone(),
        &[
            key("sort_declaration", 0),
            key("bracket_syntax_item", 0),
            key("bracket_syntax_item", 1),
            key("bracket_syntax_item", 2),
            key("bracket_value_reference", 0),
        ],
        GrammarDescriptor::Production(DescriptorProduction {
            key: bracket_primary.clone(),
            template_key: None,
            owner: DescriptorProductionOwner::BracketSort {
                sort: DescriptorSortReference {
                    key: key("sort_declaration", 0),
                    sort: DescriptorSortRef::Declared(expr_sort.clone()),
                },
            },
            result_sort: DescriptorSortReference {
                key: key("sort_declaration", 0),
                sort: DescriptorSortRef::Declared(item("Expr", ItemKind::Sort)),
            },
            items: vec![
                DescriptorProductionItem::Terminal {
                    key: key("bracket_syntax_item", 0),
                    text: "(".into(),
                },
                DescriptorProductionItem::NonTerminal {
                    key: key("bracket_syntax_item", 1),
                    field_key: key("bracket_value_reference", 0),
                    declaration_key: None,
                    field: ProductionFieldId::new("value").unwrap(),
                    sort: Box::new(DescriptorSortReference {
                        key: key("sort_declaration", 0),
                        sort: DescriptorSortRef::Declared(expr_sort),
                    }),
                },
                DescriptorProductionItem::Terminal {
                    key: key("bracket_syntax_item", 2),
                    text: ")".into(),
                },
            ],
            attributes: vec![DescriptorProductionAttribute::Bracket {
                key: bracket_primary,
            }],
        }),
    );

    let subsort_primary = key("subsort_declaration", 0);
    let subsort = grammar_descriptor(
        item("__subsort_Int_Value", ItemKind::Grammar),
        subsort_primary.clone(),
        &[key("subsort_sub_sort", 0), key("subsort_super_sort", 0)],
        GrammarDescriptor::Subsort {
            key: subsort_primary,
            subsort: DescriptorSortReference {
                key: key("subsort_sub_sort", 0),
                sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
            },
            supersort: declared_sort("subsort_super_sort", 0, value_sort),
        },
    );

    let precedence_primary = key("precedence_declaration", 0);
    let precedence = grammar_descriptor(
        item("__precedence_0", ItemKind::Grammar),
        precedence_primary.clone(),
        &[
            key("precedence_chain", 0),
            key("precedence_group_reference", 0),
            key("precedence_group_reference", 1),
        ],
        GrammarDescriptor::Precedence {
            key: precedence_primary,
            chains: vec![DescriptorPrecedenceChain {
                key: key("precedence_chain", 0),
                groups: vec![
                    DescriptorGroupReference {
                        key: key("precedence_group_reference", 0),
                        group: ProductionGroupId::new("multiplicative").unwrap(),
                    },
                    DescriptorGroupReference {
                        key: key("precedence_group_reference", 1),
                        group: ProductionGroupId::new("additive").unwrap(),
                    },
                ],
            }],
        },
    );

    let associativity_primary = key("associativity_declaration", 0);
    let associativity = grammar_descriptor(
        item("__associativity_0", ItemKind::Grammar),
        associativity_primary.clone(),
        &[
            key("associativity_sentence", 0),
            key("associativity_group_reference", 0),
            key("associativity_group_reference", 1),
        ],
        GrammarDescriptor::Associativity {
            key: associativity_primary,
            sentences: vec![DescriptorAssociativitySentence {
                key: key("associativity_sentence", 0),
                associativity: GroupAssociativity::Left,
                groups: vec![
                    DescriptorGroupReference {
                        key: key("associativity_group_reference", 0),
                        group: ProductionGroupId::new("multiplicative").unwrap(),
                    },
                    DescriptorGroupReference {
                        key: key("associativity_group_reference", 1),
                        group: ProductionGroupId::new("additive").unwrap(),
                    },
                ],
            }],
        },
    );

    let mut guarded_token = token.clone();
    let [DescriptorProductionItem::RegexTerminal { precede_regex, .. }] =
        expression_production(&mut guarded_token)
            .items
            .as_mut_slice()
    else {
        unreachable!()
    };
    *precede_regex = Some("[a-z]".into());
    assert!(matches!(
        guarded_token.validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidProduction(
            "nominal token regex cannot carry precede/follow guards"
        ))
    ));

    let mut regex_bracket = bracket.clone();
    expression_production(&mut regex_bracket).items[0] = DescriptorProductionItem::RegexTerminal {
        key: key("bracket_syntax_item", 0),
        precede_regex: None,
        regex: "[(]".into(),
        follow_regex: None,
    };
    assert!(matches!(
        regex_bracket.validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidProduction(
            "bracket production cannot contain regex items"
        ))
    ));

    let mut wrong_field_bracket = bracket.clone();
    let DescriptorProductionItem::NonTerminal { field, .. } =
        &mut expression_production(&mut wrong_field_bracket).items[1]
    else {
        unreachable!()
    };
    *field = ProductionFieldId::new("inner").unwrap();
    assert!(matches!(
        wrong_field_bracket.validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidProduction(
            "bracket nonterminal field must be `value`"
        ))
    ));

    let mut wrong_sort_bracket = bracket.clone();
    expression_production(&mut wrong_sort_bracket)
        .result_sort
        .sort = DescriptorSortRef::Declared(item("OtherExpr", ItemKind::Sort));
    assert!(matches!(
        wrong_sort_bracket.validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidProduction(
            "bracket owner and result sorts must be identical"
        ))
    ));

    let descriptors = vec![token, bracket, subsort, precedence, associativity];
    for descriptor in &descriptors {
        descriptor.validate_v6_contract().unwrap();
    }
    let json = DescriptorBundle::new(descriptors)
        .to_canonical_json()
        .unwrap();
    let decoded: DescriptorBundle = serde_json::from_str(&json).unwrap();
    assert_eq!(decoded.descriptors.len(), 5);
    assert!(json.contains("\"sort_source\": \"builtin\""));
    assert!(json.contains("\"grammar_kind\": \"precedence\""));
    assert!(json.contains("\"grammar_kind\": \"associativity\""));
}

#[test]
fn format_requires_explicit_constructor_syntax() {
    let mut descriptors = expression_descriptors();
    expression_production(&mut descriptors[0]).template_key = None;
    assert!(matches!(
        descriptors[0].validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidProduction(
            "format metadata requires explicit constructor syntax"
        ))
    ));
}

#[test]
fn wrong_kinds_missing_origins_and_noncanonical_literals_are_rejected() {
    let mut descriptors = expression_descriptors();
    descriptors[0].id = item("wrong", ItemKind::Rule);
    assert!(matches!(
        descriptors[0].validate_v6_contract(),
        Err(ProtocolV6ShapeError::DescriptorItemKind { .. })
    ));

    let mut descriptors = expression_descriptors();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptors[1].payload else {
        unreachable!()
    };
    rule.result = DescriptorTerm::Literal {
        key: key("missing_literal", 0),
        literal: DescriptorLiteral::Int("1_000".into()),
    };
    assert!(matches!(
        descriptors[1].validate_v6_contract(),
        Err(ProtocolV6ShapeError::MissingProvenance(_))
    ));

    let mut descriptors = expression_descriptors();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptors[1].payload else {
        unreachable!()
    };
    rule.result = DescriptorTerm::Wildcard {
        key: key("rule_left_wildcard", 0),
    };
    assert!(matches!(
        descriptors[1].validate_v6_contract(),
        Err(ProtocolV6ShapeError::InvalidTerm(_))
    ));
}

macro_rules! type_keys {
    ($($name:ident => $ty:ty),+ $(,)?) => {
        $(fn $name() -> TypeId { TypeId::of::<$ty>() })+
    };
}

type_keys! {
    k_sequence_key => u8,
    int_key => u16,
    bool_key => u32,
    map_key => i8,
    id_key => i16,
    bytes_key => i32,
    int_add_key => (u8, u8),
    int_sub_key => (u8, u16),
    int_mul_key => (u8, u32),
    int_tdiv_key => (u8, u64),
    int_ge_key => (u16, u8),
    int_gt_key => (u16, u16),
    int_le_key => (u16, u32),
    int_lt_key => (u16, u64),
    int_eq_key => (u32, u8),
    int_ne_key => (u32, u16),
    bool_not_key => (u32, u32),
    bool_eq_key => (u32, u64),
    bool_ne_key => (u64, u8),
    bool_and_key => (u64, u16),
    bool_or_key => (u64, u32),
    bytes_length_key => (i64, u8),
    bytes_get_key => (i64, u16),
    map_update_key => (u64, u64),
}

fn registry() -> HostBuiltinRegistry {
    let sorts = [
        (BuiltinSort::KSequence, k_sequence_key as fn() -> TypeId),
        (BuiltinSort::Int, int_key),
        (BuiltinSort::Bool, bool_key),
        (BuiltinSort::Map, map_key),
        (BuiltinSort::Id, id_key),
        (BuiltinSort::Bytes, bytes_key),
    ]
    .into_iter()
    .map(|(sort, key)| HostBuiltinSortRegistration {
        sort,
        target: HostTypeKey(key),
    })
    .collect();
    let operations = [
        (BuiltinOperation::IntAdd, int_add_key as fn() -> TypeId),
        (BuiltinOperation::IntSub, int_sub_key),
        (BuiltinOperation::IntMul, int_mul_key),
        (BuiltinOperation::IntTDiv, int_tdiv_key),
        (BuiltinOperation::IntGreaterEqual, int_ge_key),
        (BuiltinOperation::IntGreater, int_gt_key),
        (BuiltinOperation::IntLessEqual, int_le_key),
        (BuiltinOperation::IntLess, int_lt_key),
        (BuiltinOperation::IntEqual, int_eq_key),
        (BuiltinOperation::IntNotEqual, int_ne_key),
        (BuiltinOperation::BoolNot, bool_not_key),
        (BuiltinOperation::BoolEqual, bool_eq_key),
        (BuiltinOperation::BoolNotEqual, bool_ne_key),
        (BuiltinOperation::BoolAnd, bool_and_key),
        (BuiltinOperation::BoolOr, bool_or_key),
        (BuiltinOperation::BytesLength, bytes_length_key),
        (BuiltinOperation::BytesGet, bytes_get_key),
    ]
    .into_iter()
    .map(|(operation, key)| HostBuiltinOperationRegistration {
        operation,
        target: HostTypeKey(key),
    })
    .collect();
    let map_operations = vec![HostMapOperationRegistration {
        operation: MapOperation::Update,
        target: HostTypeKey(map_update_key),
    }];
    HostBuiltinRegistry {
        sorts,
        operations,
        map_operations,
    }
}

#[test]
fn builtin_registry_is_complete_exact_and_alias_safe() {
    let registry = registry();
    registry.validate().unwrap();
    assert_eq!(
        registry.resolve_sort(TypeId::of::<u16>()),
        Some(BuiltinSort::Int)
    );
    assert_eq!(
        registry.resolve_sort(TypeId::of::<IntAlias>()),
        Some(BuiltinSort::Int)
    );
    assert_eq!(
        registry.resolve_operation(int_tdiv_key()),
        Some(BuiltinOperation::IntTDiv)
    );
    assert_eq!(
        registry.resolve_map_operation(map_update_key()),
        Some(MapOperation::Update)
    );

    let mut incomplete = registry.clone();
    incomplete.operations.pop();
    assert_eq!(
        incomplete.validate(),
        Err(HostBuiltinRegistryError::MissingOperation(
            BuiltinOperation::BytesGet
        ))
    );
    let mut missing_map = registry.clone();
    missing_map.map_operations.clear();
    assert_eq!(
        missing_map.validate(),
        Err(HostBuiltinRegistryError::MissingMapOperation(
            MapOperation::Update
        ))
    );
    let mut unsupported = registry.clone();
    unsupported.map_operations[0].operation = MapOperation::Item;
    assert_eq!(
        unsupported.validate(),
        Err(HostBuiltinRegistryError::UnsupportedMapOperation(
            MapOperation::Item
        ))
    );
    let mut duplicate = registry.clone();
    duplicate.map_operations.push(duplicate.map_operations[0]);
    assert_eq!(
        duplicate.validate(),
        Err(HostBuiltinRegistryError::DuplicateMapOperation(
            MapOperation::Update
        ))
    );
    let mut collision = registry.clone();
    collision.operations[0].target = HostTypeKey(int_key);
    assert_eq!(
        collision.validate(),
        Err(HostBuiltinRegistryError::ReusedRustType)
    );
    let mut map_collision = registry;
    map_collision.map_operations[0].target = HostTypeKey(int_key);
    assert_eq!(
        map_collision.validate(),
        Err(HostBuiltinRegistryError::ReusedRustType)
    );
}

fn add_key() -> TypeId {
    TypeId::of::<Add>()
}

fn add_alias_key() -> TypeId {
    TypeId::of::<AddAlias>()
}

fn boolean_key() -> TypeId {
    TypeId::of::<Boolean>()
}

fn boolean_type_alias_key() -> TypeId {
    TypeId::of::<BooleanTypeAlias>()
}

fn boolean_use_alias_key() -> TypeId {
    TypeId::of::<BooleanUseAlias>()
}

fn boolean_reexport_alias_key() -> TypeId {
    TypeId::of::<boolean_api::ReexportAlias>()
}

fn false_variant_key() -> TypeId {
    Boolean::__krs_variant_key_False()
}

fn false_type_alias_variant_key() -> TypeId {
    BooleanTypeAlias::__krs_variant_key_False()
}

fn false_use_alias_variant_key() -> TypeId {
    BooleanUseAlias::__krs_variant_key_False()
}

fn false_reexport_alias_variant_key() -> TypeId {
    boolean_api::ReexportAlias::__krs_variant_key_False()
}

fn true_variant_key() -> TypeId {
    Boolean::__krs_variant_key_True()
}

fn other_boolean_key() -> TypeId {
    TypeId::of::<OtherBoolean>()
}

fn other_false_variant_key() -> TypeId {
    OtherBoolean::__krs_variant_key_False()
}

fn type_reference(key: fn() -> TypeId, path: &str) -> HostTypeReference {
    HostTypeReference {
        key: HostTypeKey(key),
        authored_path: path.into(),
    }
}

fn variant_target(
    enum_key: fn() -> TypeId,
    variant_key: fn() -> TypeId,
    owner_path: &str,
    full_path: &str,
) -> HostApplicationTarget {
    HostApplicationTarget::EnumVariant(
        HostEnumVariantReference::new(
            type_reference(enum_key, owner_path),
            HostTypeKey(variant_key),
            full_path,
        )
        .unwrap(),
    )
}

#[test]
fn enum_variant_identity_is_an_exact_alias_safe_owner_marker_pair() {
    let _: Boolean = BooleanTypeAlias::False;
    let _: Boolean = BooleanUseAlias::False;
    let _: Boolean = boolean_api::ReexportAlias::False;

    let declared_false = HostDeclarationIdentity::EnumVariant(HostEnumVariantKey::new(
        HostTypeKey(boolean_key),
        HostTypeKey(false_variant_key),
    ));
    let expected = declared_false.resolve();
    assert_eq!(
        expected,
        HostApplicationIdentity::EnumVariant {
            enum_type: TypeId::of::<Boolean>(),
            variant: TypeId::of::<FalseVariantMarker>(),
        }
    );

    let references = [
        variant_target(boolean_key, false_variant_key, "Boolean", "Boolean::False"),
        variant_target(
            boolean_type_alias_key,
            false_type_alias_variant_key,
            "BooleanTypeAlias",
            "BooleanTypeAlias::False",
        ),
        variant_target(
            boolean_use_alias_key,
            false_use_alias_variant_key,
            "BooleanUseAlias",
            "BooleanUseAlias::False",
        ),
        variant_target(
            boolean_reexport_alias_key,
            false_reexport_alias_variant_key,
            "boolean_api::ReexportAlias",
            "boolean_api::ReexportAlias::False",
        ),
    ];
    for reference in references {
        assert_eq!(reference.resolve(), expected);
    }

    let true_variant = HostDeclarationIdentity::EnumVariant(HostEnumVariantKey::new(
        HostTypeKey(boolean_key),
        HostTypeKey(true_variant_key),
    ));
    assert_ne!(true_variant.resolve(), expected);

    let same_spelling_other_enum = HostDeclarationIdentity::EnumVariant(HostEnumVariantKey::new(
        HostTypeKey(other_boolean_key),
        HostTypeKey(other_false_variant_key),
    ));
    assert_ne!(same_spelling_other_enum.resolve(), expected);

    let boolean_false = StableItemId::new(
        package(),
        ["expr"],
        "False",
        ItemKind::Constructor,
        enum_variant_disambiguator("Boolean").unwrap(),
    )
    .unwrap();
    let other_false = StableItemId::new(
        package(),
        ["expr"],
        "False",
        ItemKind::Constructor,
        enum_variant_disambiguator("OtherBoolean").unwrap(),
    )
    .unwrap();
    let struct_false = item("False", ItemKind::Constructor);
    assert_ne!(boolean_false, other_false);
    assert_ne!(boolean_false, struct_false);
    assert_eq!(boolean_false.item_name(), "False");
    assert_eq!(boolean_false.disambiguator(), "enum:Boolean");
}

#[test]
fn nominal_struct_identity_remains_alias_safe_and_record_fields_remain_stable() {
    let declaration = HostDeclarationIdentity::Nominal(HostTypeKey(add_key));
    let reference = HostApplicationTarget::Nominal(type_reference(add_alias_key, "AddAlias"));
    assert_eq!(declaration.resolve(), reference.resolve());
    assert_eq!(
        declaration.resolve(),
        HostApplicationIdentity::Nominal(TypeId::of::<Add>())
    );

    let lhs = ProductionFieldId::new("lhs").unwrap();
    let rhs = ProductionFieldId::new("rhs").unwrap();
    assert_ne!(lhs, rhs);
    assert_eq!(ProductionFieldId::new("lhs").unwrap(), lhs);
}

#[test]
fn standalone_variant_aliases_and_mismatched_owner_paths_are_rejected() {
    let _: Boolean = StandaloneFalse;
    let standalone = HostEnumVariantReference::new(
        type_reference(boolean_key, "Boolean"),
        HostTypeKey(false_variant_key),
        "StandaloneFalse",
    );
    assert_eq!(
        standalone.unwrap_err(),
        HostEnumVariantReferenceError::UnqualifiedPath("StandaloneFalse".into())
    );

    let mismatch = HostEnumVariantReference::new(
        type_reference(boolean_key, "BooleanUseAlias"),
        HostTypeKey(false_variant_key),
        "Boolean::False",
    );
    assert_eq!(
        mismatch.unwrap_err(),
        HostEnumVariantReferenceError::OwnerPathMismatch {
            owner: "BooleanUseAlias".into(),
            application: "Boolean::False".into(),
        }
    );
}

#[test]
fn protocol_five_is_rejected_without_compatibility_guessing() {
    let error = serde_json::from_str::<DescriptorBundle>(
        r#"{"protocol_version":5,"descriptors":[],"declarations":[]}"#,
    )
    .unwrap_err();
    assert!(error.to_string().contains("expected 17"));
}

fn first_object_with_key_mut<'a>(
    value: &'a mut serde_json::Value,
    key: &str,
) -> Option<&'a mut serde_json::Map<String, serde_json::Value>> {
    match value {
        serde_json::Value::Object(object) => {
            if object.contains_key(key) {
                return Some(object);
            }
            object
                .values_mut()
                .find_map(|value| first_object_with_key_mut(value, key))
        }
        serde_json::Value::Array(values) => values
            .iter_mut()
            .find_map(|value| first_object_with_key_mut(value, key)),
        serde_json::Value::Null
        | serde_json::Value::Bool(_)
        | serde_json::Value::Number(_)
        | serde_json::Value::String(_) => None,
    }
}

#[test]
fn future_and_adapter_fields_are_rejected_at_every_protocol_boundary() {
    let json = DescriptorBundle::new(expression_descriptors())
        .to_canonical_json()
        .unwrap();
    let mut outer = serde_json::from_str::<serde_json::Value>(&json).unwrap();
    outer["descriptors"][0]
        .as_object_mut()
        .unwrap()
        .insert("raw_label".into(), "_+Int_".into());
    let error = serde_json::from_value::<DescriptorBundle>(outer).unwrap_err();
    assert!(error.to_string().contains("raw_label"));

    let mut nested = serde_json::from_str::<serde_json::Value>(&json).unwrap();
    first_object_with_key_mut(&mut nested, "term_kind")
        .unwrap()
        .insert("adapter_id".into(), "production-42".into());
    let error = serde_json::from_value::<DescriptorBundle>(nested).unwrap_err();
    assert!(error.to_string().contains("adapter_id"));
}

#[test]
fn swapped_roles_and_orphaned_provenance_are_rejected() {
    let mut descriptors = expression_descriptors();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptors[1].payload else {
        unreachable!()
    };
    let DescriptorTerm::Variable {
        key: variable_key, ..
    } = &mut rule.result
    else {
        unreachable!()
    };
    *variable_key = key("rule_result_type", 0);
    assert!(matches!(
        descriptors[1].validate_v6_contract(),
        Err(ProtocolV6ShapeError::UnexpectedProvenance { .. })
    ));

    let mut descriptors = expression_descriptors();
    let primary = descriptors[0].provenance.primary_key().clone();
    let mut origins = descriptors[0].provenance.origins().to_vec();
    origins.push(DescriptorNodeOrigin::new(
        key("adapter_production_id", 0),
        origin(99),
    ));
    descriptors[0].provenance = DescriptorProvenance::new(primary, origins).unwrap();
    assert!(matches!(
        descriptors[0].validate_v6_contract(),
        Err(ProtocolV6ShapeError::ExtraProvenance(_))
    ));
}
