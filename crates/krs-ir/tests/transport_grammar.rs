//! Grammar and structured-rule transport contract tests.

use krs_ir::testing::DescriptorInputs;

use std::any::TypeId;
use std::collections::{BTreeMap, BTreeSet};

use krs_ir::testing;
use krs_ir::transport::detail::{
    GrammarApplicationReason, GrammarProductionReason, GrammarTermReason,
};
use krs_ir::{
    ArgumentsError, BuiltinOperation, BuiltinSort, DescriptorApplicationHeadClass,
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorAssociativitySentence,
    DescriptorBundle, DescriptorFieldReference, DescriptorFormatFragment, DescriptorGroupReference,
    DescriptorLexicalPrecedence, DescriptorLiteral, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorPrecedenceChain, DescriptorProduction, DescriptorProductionAttribute,
    DescriptorProductionItem, DescriptorProductionOwner, DescriptorProvenance,
    DescriptorRuleCondition, DescriptorRuleLabel, DescriptorSortRef, DescriptorSortReference,
    DescriptorTerm, DescriptorTermArgument, FormatFragment, GrammarDescriptor,
    GrammarTransportError, GroupAssociativity, HostApplicationIdentity, HostApplicationTarget,
    HostBuiltinRegistry, HostBuiltinRegistryError, HostDeclarationIdentity, HostEnumVariantKey,
    HostEnumVariantReference, HostEnumVariantReferenceError, HostTypeKey, HostTypeReference,
    ItemKind, ListOperation, MapOperation, OriginStack, PackageId, ProductionFieldId,
    ProductionGroupId, ProvenanceKey, ProvenanceRole, SentenceKind, SetOperation, StableItemId,
    StrictnessKind, StructuredRuleDescriptor, TermMapOperation, enum_variant_disambiguator,
};

type IntAlias = u16;

struct Add;

type AddAlias = Add;

#[expect(
    dead_code,
    reason = "The fixture uses enum type identity without constructing every variant."
)]
enum Boolean {
    True,
    False,
}

struct TrueVariantMarker;

struct FalseVariantMarker;

#[expect(
    non_snake_case,
    reason = "The fixture mirrors generated variant-key method names."
)]
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

#[expect(
    dead_code,
    reason = "The fixture uses enum type identity without constructing its variant."
)]
enum OtherBoolean {
    False,
}

struct OtherFalseVariantMarker;

#[expect(
    non_snake_case,
    reason = "The fixture mirrors generated variant-key method names."
)]
impl OtherBoolean {
    fn __krs_variant_key_False() -> TypeId {
        TypeId::of::<OtherFalseVariantMarker>()
    }
}

fn package() -> PackageId {
    testing::package("IMP", "imp-semantics")
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "expr", name, kind)
}

fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal)
}

fn origin(start: u32) -> OriginStack {
    testing::authored_in(
        package(),
        "src/expr.rs",
        testing::digest_with("1234567890abcdef".repeat(4)),
        start,
        start + 1,
    )
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

fn declared_sort(role: ProvenanceRole, ordinal: u32, id: StableItemId) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(role, ordinal),
        sort: DescriptorSortRef::Declared(id),
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Enumerates the complete descriptor test fixtures."
)]
fn expression_descriptors() -> Vec<DescriptorInputs> {
    let expr = item("Expr", ItemKind::Sort);
    let value = item("Value", ItemKind::Sort);
    let add = item("Add", ItemKind::Constructor);
    let grammar_id = item("__grammar_Add", ItemKind::Grammar);
    let rule_id = item("add_zero", ItemKind::Rule);

    let grammar_primary = key(ProvenanceRole::ConstructorDeclaration, 0);
    let grammar_keys = [
        key(ProvenanceRole::ConstructorSort, 0),
        key(ProvenanceRole::ConstructorSyntax, 0),
        key(ProvenanceRole::ConstructorSyntaxItem, 0),
        key(ProvenanceRole::ConstructorSyntaxItem, 1),
        key(ProvenanceRole::ConstructorSyntaxItem, 2),
        key(ProvenanceRole::ConstructorSyntaxFieldReference, 0),
        key(ProvenanceRole::ConstructorSyntaxFieldReference, 1),
        key(ProvenanceRole::ConstructorFieldSort, 0),
        key(ProvenanceRole::ConstructorFieldSort, 1),
        key(ProvenanceRole::ConstructorFieldDeclaration, 0),
        key(ProvenanceRole::ConstructorFieldDeclaration, 1),
        key(ProvenanceRole::ConstructorGroup, 0),
        key(ProvenanceRole::ConstructorAvoid, 0),
        key(ProvenanceRole::ConstructorFormat, 0),
        key(ProvenanceRole::ConstructorFormatFragment, 0),
        key(ProvenanceRole::ConstructorFormatFragment, 1),
        key(ProvenanceRole::ConstructorFormatFragment, 2),
        key(ProvenanceRole::ConstructorDocumentation, 0),
        key(ProvenanceRole::ConstructorDocumentation, 1),
        key(ProvenanceRole::StrictnessDeclaration, 0),
        key(ProvenanceRole::StrictnessFieldReference, 0),
        key(ProvenanceRole::StrictnessFieldReference, 1),
        key(ProvenanceRole::StrictnessResultSort, 0),
    ];
    let grammar = DescriptorInputs::new(
        grammar_id,
        BTreeMap::new(),
        provenance(grammar_primary.clone(), &grammar_keys),
        DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Production(
            DescriptorProduction {
                key: grammar_primary.clone(),
                template_key: Some(key(ProvenanceRole::ConstructorSyntax, 0)),
                owner: DescriptorProductionOwner::Constructor {
                    constructor: DescriptorApplicationReference {
                        key: grammar_primary,
                        application: DescriptorApplicationRef::Declared(add.clone()),
                    },
                },
                result_sort: declared_sort(ProvenanceRole::ConstructorSort, 0, expr.clone()),
                items: vec![
                    DescriptorProductionItem::NonTerminal {
                        key: key(ProvenanceRole::ConstructorSyntaxItem, 0),
                        field_key: key(ProvenanceRole::ConstructorSyntaxFieldReference, 0),
                        declaration_key: Some(key(ProvenanceRole::ConstructorFieldDeclaration, 0)),
                        field: ProductionFieldId::new("lhs").unwrap(),
                        sort: Box::new(declared_sort(
                            ProvenanceRole::ConstructorFieldSort,
                            0,
                            expr.clone(),
                        )),
                    },
                    DescriptorProductionItem::Terminal {
                        key: key(ProvenanceRole::ConstructorSyntaxItem, 1),
                        text: "+".into(),
                    },
                    DescriptorProductionItem::NonTerminal {
                        key: key(ProvenanceRole::ConstructorSyntaxItem, 2),
                        field_key: key(ProvenanceRole::ConstructorSyntaxFieldReference, 1),
                        declaration_key: Some(key(ProvenanceRole::ConstructorFieldDeclaration, 1)),
                        field: ProductionFieldId::new("rhs").unwrap(),
                        sort: Box::new(declared_sort(
                            ProvenanceRole::ConstructorFieldSort,
                            1,
                            expr.clone(),
                        )),
                    },
                ],
                attributes: vec![
                    DescriptorProductionAttribute::Documentation {
                        key: key(ProvenanceRole::ConstructorDocumentation, 0),
                        text: "Adds two values.".into(),
                    },
                    DescriptorProductionAttribute::Documentation {
                        key: key(ProvenanceRole::ConstructorDocumentation, 1),
                        text: "Evaluation is sequential.".into(),
                    },
                    DescriptorProductionAttribute::Group {
                        reference: DescriptorGroupReference {
                            key: key(ProvenanceRole::ConstructorGroup, 0),
                            group: ProductionGroupId::new("additive").unwrap(),
                        },
                    },
                    DescriptorProductionAttribute::Avoid {
                        key: key(ProvenanceRole::ConstructorAvoid, 0),
                    },
                    DescriptorProductionAttribute::Format {
                        key: key(ProvenanceRole::ConstructorFormat, 0),
                        fragments: vec![
                            DescriptorFormatFragment {
                                key: key(ProvenanceRole::ConstructorFormatFragment, 0),
                                fragment: FormatFragment::Item(1),
                            },
                            DescriptorFormatFragment {
                                key: key(ProvenanceRole::ConstructorFormatFragment, 1),
                                fragment: FormatFragment::Literal(" ".into()),
                            },
                            DescriptorFormatFragment {
                                key: key(ProvenanceRole::ConstructorFormatFragment, 2),
                                fragment: FormatFragment::Item(3),
                            },
                        ],
                    },
                    DescriptorProductionAttribute::Strictness {
                        key: key(ProvenanceRole::StrictnessDeclaration, 0),
                        kind: StrictnessKind::SeqStrict,
                        using: None,
                        fields: vec![
                            DescriptorFieldReference {
                                key: key(ProvenanceRole::StrictnessFieldReference, 0),
                                field: ProductionFieldId::new("lhs").unwrap(),
                            },
                            DescriptorFieldReference {
                                key: key(ProvenanceRole::StrictnessFieldReference, 1),
                                field: ProductionFieldId::new("rhs").unwrap(),
                            },
                        ],
                        result_sort: Box::new(declared_sort(
                            ProvenanceRole::StrictnessResultSort,
                            0,
                            value,
                        )),
                    },
                ],
            },
        ))),
    );

    let rule_primary = key(ProvenanceRole::RuleDeclaration, 0);
    let rule_keys = [
        key(ProvenanceRole::RuleType, 0),
        key(ProvenanceRole::RuleResultType, 0),
        key(ProvenanceRole::RulePattern, 0),
        key(ProvenanceRole::RuleResult, 0),
        key(ProvenanceRole::RuleLeftPath, 0),
        key(ProvenanceRole::RuleLeftPath, 1),
        key(ProvenanceRole::RuleRightPath, 0),
        key(ProvenanceRole::RuleLeftApplicationHead, 0),
        key(ProvenanceRole::RuleLeftRecordFieldName, 0),
        key(ProvenanceRole::RuleLeftRecordFieldName, 1),
        key(ProvenanceRole::RuleLeftReference, 0),
        key(ProvenanceRole::RuleLeftWildcard, 0),
        key(ProvenanceRole::RuleRightReference, 0),
    ];
    let variable = || DescriptorTerm::Variable {
        key: key(ProvenanceRole::RuleLeftReference, 0),
        path_key: key(ProvenanceRole::RuleLeftPath, 1),
        name: "x".into(),
    };
    let rule = DescriptorInputs::new(
        rule_id,
        BTreeMap::new(),
        provenance(rule_primary, &rule_keys),
        DescriptorPayload::StructuredRule(Box::new(StructuredRuleDescriptor {
            sentence_kind: SentenceKind::Transition,
            label: None,
            requires: None,
            priority: None,
            simplification: None,
            pattern_key: key(ProvenanceRole::RulePattern, 0),
            result_key: key(ProvenanceRole::RuleResult, 0),
            subject_sort: declared_sort(ProvenanceRole::RuleType, 0, expr.clone()),
            result_sort: declared_sort(ProvenanceRole::RuleResultType, 0, expr),
            bindings: vec!["x".into()],
            subject: DescriptorTerm::Application {
                head_class: DescriptorApplicationHeadClass::Applied,
                reference: DescriptorApplicationReference {
                    key: key(ProvenanceRole::RuleLeftApplicationHead, 0),
                    application: DescriptorApplicationRef::Declared(add),
                },
                path_key: key(ProvenanceRole::RuleLeftPath, 0),
                arguments: vec![
                    DescriptorTermArgument::Named {
                        key: key(ProvenanceRole::RuleLeftRecordFieldName, 0),
                        field: ProductionFieldId::new("rhs").unwrap(),
                        value: Box::new(DescriptorTerm::Wildcard {
                            key: key(ProvenanceRole::RuleLeftWildcard, 0),
                        }),
                    },
                    DescriptorTermArgument::Named {
                        key: key(ProvenanceRole::RuleLeftRecordFieldName, 1),
                        field: ProductionFieldId::new("lhs").unwrap(),
                        value: Box::new(variable()),
                    },
                ]
                .try_into()
                .unwrap(),
            },
            result: DescriptorTerm::Variable {
                key: key(ProvenanceRole::RuleRightReference, 0),
                path_key: key(ProvenanceRole::RuleRightPath, 0),
                name: "x".into(),
            },
        })),
    );
    vec![grammar, rule]
}

#[test]
fn expression_grammar_and_rule_round_trip_deterministically() {
    let descriptors = expression_descriptors();
    for descriptor in &descriptors {
        descriptor.build().unwrap();
    }
    let bundle = krs_ir::testing::descriptor_bundle(descriptors).unwrap();
    testing::assert_canonical_contract(&bundle);
    let forward = bundle.to_canonical_json().unwrap();
    assert!(forward.contains(&format!(
        "\"protocol_version\": {}",
        krs_ir::SchemaVersion::CURRENT.0
    )));
    assert!(forward.contains("\"attribute_kind\": \"documentation\""));
    assert!(forward.contains("Adds two values."));
    assert!(forward.contains("\"structured_rule\""));
    assert!(forward.contains("\"grammar_kind\": \"production\""));
    assert!(!forward.contains("TypeId"));
    assert!(!forward.contains("_+Int_"));
    let decoded: DescriptorBundle = serde_json::from_str(&forward).unwrap();
    assert_eq!(decoded.protocol_version(), krs_ir::SchemaVersion::CURRENT);
}

#[test]
fn explicit_rule_label_requires_exact_provenance_and_a_portable_name() {
    let mut descriptors = expression_descriptors();
    let descriptor = &mut descriptors[1];
    let label_key = key(ProvenanceRole::RuleLabel, 0);
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

    descriptor.build().unwrap();
    assert_eq!(
        descriptor.provenance.origin_for(&label_key),
        Some(&origin(77))
    );

    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!()
    };
    rule.label.as_mut().unwrap().name = "if true".into();
    assert!(matches!(
        descriptor.build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::InvalidTerm(GrammarTermReason::InvalidExplicitRuleLabel)
        ))
    ));
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Comprehensively tests structured rule configuration with various attribute combinations."
)]
fn structured_requires_has_closed_exact_provenance_and_pre_bindings() {
    let mut descriptors = expression_descriptors();
    let descriptor = &mut descriptors[1];
    let condition_keys = [
        key(ProvenanceRole::RuleRequires, 0),
        key(ProvenanceRole::RuleRequiresPath, 0),
        key(ProvenanceRole::RuleRequiresPath, 1),
        key(ProvenanceRole::RuleRequiresApplicationHead, 0),
        key(ProvenanceRole::RuleRequiresReference, 0),
        key(ProvenanceRole::RuleRequiresLiteral, 0),
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
        key: key(ProvenanceRole::RuleRequires, 0),
        term: DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key(ProvenanceRole::RuleRequiresApplicationHead, 0),
                application: DescriptorApplicationRef::Builtin(BuiltinOperation::IntGreater),
            },
            path_key: key(ProvenanceRole::RuleRequiresPath, 0),
            arguments: vec![
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Variable {
                        key: key(ProvenanceRole::RuleRequiresReference, 0),
                        path_key: key(ProvenanceRole::RuleRequiresPath, 1),
                        name: "x".into(),
                    }),
                },
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Literal {
                        key: key(ProvenanceRole::RuleRequiresLiteral, 0),
                        literal: DescriptorLiteral::Int("0".into()),
                    }),
                },
            ]
            .try_into()
            .unwrap(),
        },
    });

    descriptor.build().unwrap();
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
    *path_key = key(ProvenanceRole::RuleRequiresPath, 1);
    assert!(matches!(
        wrong_path.build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::UnexpectedProvenance { .. }
        ))
    ));

    let mut unbound = descriptor.clone();
    let DescriptorPayload::StructuredRule(rule) = &mut unbound.payload else {
        unreachable!()
    };
    let DescriptorTerm::Application { arguments, .. } = &mut rule.requires.as_mut().unwrap().term
    else {
        unreachable!()
    };
    let krs_ir::Arguments::Positional(arguments) = arguments else {
        unreachable!()
    };
    let value = &mut arguments[0];
    let DescriptorTerm::Variable { name, .. } = value.as_mut() else {
        unreachable!()
    };
    *name = "post_only".into();
    assert!(matches!(
        unbound.build(),
        Err(krs_ir::DescriptorError::Grammar(GrammarTransportError::InvalidBinding(name))) if name == "post_only"
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
    let krs_ir::Arguments::Positional(arguments) = arguments else {
        unreachable!()
    };
    let value = &mut arguments[0];
    let DescriptorTerm::Variable { name, .. } = value.as_mut() else {
        unreachable!()
    };
    *name = "post_only".into();
    assert!(matches!(
        post_only.build(),
        Err(krs_ir::DescriptorError::Grammar(GrammarTransportError::InvalidBinding(name))) if name == "post_only"
    ));
}

fn expression_production(descriptor: &mut DescriptorInputs) -> &mut DescriptorProduction {
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
    *key = crate_key(ProvenanceRole::ConstructorSyntaxItem, 0);
    *field_key = crate_key(ProvenanceRole::ConstructorSyntaxFieldReference, 0);
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
    *key = crate_key(ProvenanceRole::ConstructorSyntaxItem, 2);
    *field_key = crate_key(ProvenanceRole::ConstructorSyntaxFieldReference, 1);
    *field = ProductionFieldId::new("lhs").unwrap();
}

fn crate_key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    key(role, ordinal)
}

#[test]
fn explicit_constructor_syntax_tracks_occurrence_and_declaration_ordinals_separately() {
    let mut descriptors = expression_descriptors();
    reorder_expression_fields(expression_production(&mut descriptors[0]));
    descriptors[0].build().unwrap();

    let production = expression_production(&mut descriptors[0]);
    let DescriptorProductionItem::NonTerminal { field_key, .. } = &mut production.items[0] else {
        unreachable!()
    };
    *field_key = key(ProvenanceRole::ConstructorSyntaxFieldReference, 1);
    assert!(matches!(
        descriptors[0].build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::UnexpectedProvenance { .. }
        ))
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
    *declaration_key = Some(key(ProvenanceRole::ConstructorFieldDeclaration, 1));
    sort.key = key(ProvenanceRole::ConstructorFieldSort, 1);
    assert!(matches!(
        descriptors[0].build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::InvalidProduction(
                GrammarProductionReason::DuplicateConstructorFieldOrdinal
            )
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
            key: key(ProvenanceRole::RuleRightReference, 0),
            application: DescriptorApplicationRef::Declared(item("False", ItemKind::Constructor)),
        },
        path_key: key(ProvenanceRole::RuleRightPath, 0),
        arguments: vec![].try_into().unwrap(),
    };
    descriptors[1].build().unwrap();
    let bundle = krs_ir::testing::descriptor_bundle(descriptors).unwrap();
    testing::assert_canonical_contract(&bundle);
    let json = bundle.to_canonical_json().unwrap();
    assert!(json.contains("\"head_class\": \"bare_reference\""));

    let mut descriptors = expression_descriptors();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptors[1].payload else {
        unreachable!()
    };
    rule.result = DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::BareReference,
        reference: DescriptorApplicationReference {
            key: key(ProvenanceRole::RuleRightReference, 0),
            application: DescriptorApplicationRef::Declared(item("False", ItemKind::Constructor)),
        },
        path_key: key(ProvenanceRole::RuleRightPath, 0),
        arguments: vec![DescriptorTermArgument::Positional {
            value: Box::new(DescriptorTerm::Literal {
                key: key(ProvenanceRole::RuleRightLiteral, 0),
                literal: DescriptorLiteral::Int("0".into()),
            }),
        }]
        .try_into()
        .unwrap(),
    };
    assert!(matches!(
        descriptors[1].build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::InvalidApplication(
                GrammarApplicationReason::BareConstructorArguments
            )
        ))
    ));
}

#[test]
fn builtin_references_are_typed_and_raw_labels_are_unrepresentable() {
    let reference = DescriptorApplicationReference {
        key: key(ProvenanceRole::RuleRightApplicationHead, 0),
        application: DescriptorApplicationRef::Builtin(BuiltinOperation::IntTDiv),
    };
    let json = serde_json::to_string(&reference).unwrap();
    assert!(json.contains("int_t_div"));
    assert!(!json.contains("_/Int_"));
    let sort = DescriptorSortReference {
        key: key(ProvenanceRole::RuleResultType, 0),
        sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
    };
    assert!(sort.sort.validate().is_ok());
}

#[test]
fn ordinary_map_references_have_closed_wire_shapes() {
    let variable = |name: &str| DescriptorTerm::Variable {
        key: key(ProvenanceRole::RuleRightReference, 0),
        path_key: key(ProvenanceRole::RuleRightPath, 0),
        name: name.to_owned(),
    };
    let application = DescriptorApplicationReference {
        key: key(ProvenanceRole::RuleRightApplicationHead, 0),
        application: DescriptorApplicationRef::Map(TermMapOperation::Update),
    };
    assert_eq!(
        serde_json::to_string(&application).unwrap(),
        r#"{"key":{"role":"rule_right_application_head","ordinal":0},"application":{"application_source":"map","application":"update"}}"#
    );
    let term = DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: application,
        path_key: key(ProvenanceRole::RuleRightPath, 0),
        arguments: krs_ir::Arguments::Positional(
            ["map", "key", "value"]
                .into_iter()
                .map(|name| Box::new(variable(name)))
                .collect(),
        ),
    };
    let bindings = ["map", "key", "value"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    term.validate(|_| true, &bindings, &mut BTreeSet::new(), false)
        .unwrap();
    for (operation, names) in [
        (TermMapOperation::Get, ["map", "key"]),
        (TermMapOperation::InKeys, ["key", "map"]),
    ] {
        let term = DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key(ProvenanceRole::RuleRightApplicationHead, 0),
                application: DescriptorApplicationRef::Map(operation),
            },
            path_key: key(ProvenanceRole::RuleRightPath, 0),
            arguments: krs_ir::Arguments::Positional(
                names
                    .into_iter()
                    .map(|name| Box::new(variable(name)))
                    .collect(),
            ),
        };
        term.validate(|_| true, &bindings, &mut BTreeSet::new(), false)
            .unwrap();
    }

    let mut wrong_arity = term.clone();
    let DescriptorTerm::Application { arguments, .. } = &mut wrong_arity else {
        unreachable!()
    };
    let krs_ir::Arguments::Positional(arguments) = arguments else {
        unreachable!()
    };
    arguments.pop();
    assert!(matches!(
        wrong_arity.validate(|_| true, &bindings, &mut BTreeSet::default(), false),
        Err(GrammarTransportError::InvalidApplication(
            GrammarApplicationReason::MapOperationHasInvalidArity
        ))
    ));

    for operation in [MapOperation::Empty, MapOperation::Item] {
        assert_eq!(
            TermMapOperation::try_from(operation),
            Err(GrammarTransportError::InvalidApplication(
                GrammarApplicationReason::StructuralMapApplication
            ))
        );
        let json = serde_json::json!({
            "application_source": "map",
            "application": operation,
        });
        let error = serde_json::from_value::<DescriptorApplicationRef>(json).unwrap_err();
        assert!(
            error.to_string().contains(
                &GrammarTransportError::InvalidApplication(
                    GrammarApplicationReason::StructuralMapApplication
                )
                .to_string()
            )
        );
    }
    for operation in TermMapOperation::ALL {
        let json = serde_json::to_value(operation).unwrap();
        assert_eq!(
            json,
            serde_json::to_value(MapOperation::from(operation)).unwrap()
        );
        assert_eq!(
            serde_json::from_value::<TermMapOperation>(json).unwrap(),
            operation
        );
    }
}

#[test]
fn ordinary_set_references_have_closed_wire_shapes_and_exact_arities() {
    let variable = |name: &str| DescriptorTerm::Variable {
        key: key(ProvenanceRole::RuleRightReference, 0),
        path_key: key(ProvenanceRole::RuleRightPath, 0),
        name: name.to_owned(),
    };
    let bindings = ["set", "value"]
        .into_iter()
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    let cases = [
        (SetOperation::Empty, Vec::<&str>::new()),
        (SetOperation::Item, vec!["value"]),
        (SetOperation::Concat, vec!["set", "set"]),
        (SetOperation::Union, vec!["set", "set"]),
        (SetOperation::Contains, vec!["value", "set"]),
    ];
    for (operation, arguments) in cases {
        let reference = DescriptorApplicationReference {
            key: key(ProvenanceRole::RuleRightApplicationHead, 0),
            application: DescriptorApplicationRef::Set(operation),
        };
        assert!(
            serde_json::to_string(&reference)
                .unwrap()
                .contains(r#""application_source":"set""#)
        );
        let term = DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference,
            path_key: key(ProvenanceRole::RuleRightPath, 0),
            arguments: arguments
                .into_iter()
                .map(|name| DescriptorTermArgument::Positional {
                    value: Box::new(variable(name)),
                })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        };
        term.validate(|_| true, &bindings, &mut BTreeSet::new(), false)
            .unwrap();
    }
}

#[test]
fn ordinary_list_references_have_closed_wire_shapes_and_exact_arities() {
    let variable = |name: &str| DescriptorTerm::Variable {
        key: key(ProvenanceRole::RuleRightReference, 0),
        path_key: key(ProvenanceRole::RuleRightPath, 0),
        name: name.to_owned(),
    };
    let bindings = ["list", "index", "value"]
        .into_iter()
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    let cases = [
        (ListOperation::Empty, Vec::<&str>::new()),
        (ListOperation::Item, vec!["value"]),
        (ListOperation::Concat, vec!["list", "list"]),
        (ListOperation::Get, vec!["list", "index"]),
        (ListOperation::Update, vec!["list", "index", "value"]),
        (ListOperation::Size, vec!["list"]),
        (ListOperation::Make, vec!["index", "value"]),
        (ListOperation::Range, vec!["list", "index", "index"]),
        (ListOperation::UpdateAll, vec!["list", "index", "list"]),
    ];
    for (operation, arguments) in cases {
        let reference = DescriptorApplicationReference {
            key: key(ProvenanceRole::RuleRightApplicationHead, 0),
            application: DescriptorApplicationRef::List(operation),
        };
        let json = serde_json::to_string(&reference).unwrap();
        assert!(json.contains(r#""application_source":"list""#));
        let term = DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference,
            path_key: key(ProvenanceRole::RuleRightPath, 0),
            arguments: arguments
                .into_iter()
                .map(|name| DescriptorTermArgument::Positional {
                    value: Box::new(variable(name)),
                })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        };
        term.validate(|_| true, &bindings, &mut BTreeSet::new(), false)
            .unwrap();
    }

    let wrong_arity = DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: DescriptorApplicationReference {
            key: key(ProvenanceRole::RuleRightApplicationHead, 0),
            application: DescriptorApplicationRef::List(ListOperation::Get),
        },
        path_key: key(ProvenanceRole::RuleRightPath, 0),
        arguments: vec![DescriptorTermArgument::Positional {
            value: Box::new(variable("list")),
        }]
        .try_into()
        .unwrap(),
    };
    assert!(matches!(
        wrong_arity.validate(|_| true, &bindings, &mut BTreeSet::new(), false),
        Err(GrammarTransportError::InvalidApplication(
            GrammarApplicationReason::ListOperationHasInvalidArity
        ))
    ));
}

fn grammar_descriptor(
    id: StableItemId,
    primary: ProvenanceKey,
    keys: &[ProvenanceKey],
    grammar: GrammarDescriptor,
) -> DescriptorInputs {
    DescriptorInputs::new(
        id,
        BTreeMap::new(),
        provenance(primary, keys),
        DescriptorPayload::Grammar(Box::new(grammar)),
    )
}

#[expect(
    clippy::too_many_lines,
    reason = "Tests complete token bracket precedence and associativity rules."
)]
#[test]
fn token_bracket_subsort_precedence_and_associativity_are_complete() {
    let id_sort = item("Id", ItemKind::Sort);
    let expr_sort = item("Expr", ItemKind::Sort);
    let value_sort = item("Value", ItemKind::Sort);

    let token_primary = key(ProvenanceRole::TokenDeclaration, 0);
    let token = grammar_descriptor(
        item("__grammar_Id", ItemKind::Grammar),
        token_primary.clone(),
        &[
            key(ProvenanceRole::TokenRegex, 0),
            key(ProvenanceRole::TokenLexicalPrecedence, 0),
        ],
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
                key: key(ProvenanceRole::TokenRegex, 0),
                precede_regex: None,
                regex: "[a-zA-Z][a-zA-Z0-9_]*".into(),
                follow_regex: None,
            }],
            attributes: vec![DescriptorProductionAttribute::Token {
                key: key(ProvenanceRole::TokenRegex, 0),
                lexical_precedence: Some(DescriptorLexicalPrecedence {
                    key: key(ProvenanceRole::TokenLexicalPrecedence, 0),
                    value: 2,
                }),
            }],
        }),
    );

    let bracket_primary = key(ProvenanceRole::BracketDeclaration, 0);
    let bracket = grammar_descriptor(
        item("__grammar_Expr_bracket_0", ItemKind::Grammar),
        bracket_primary.clone(),
        &[
            key(ProvenanceRole::SortDeclaration, 0),
            key(ProvenanceRole::BracketSyntaxItem, 0),
            key(ProvenanceRole::BracketSyntaxItem, 1),
            key(ProvenanceRole::BracketSyntaxItem, 2),
            key(ProvenanceRole::BracketValueReference, 0),
        ],
        GrammarDescriptor::Production(DescriptorProduction {
            key: bracket_primary.clone(),
            template_key: None,
            owner: DescriptorProductionOwner::BracketSort {
                sort: DescriptorSortReference {
                    key: key(ProvenanceRole::SortDeclaration, 0),
                    sort: DescriptorSortRef::Declared(expr_sort.clone()),
                },
            },
            result_sort: DescriptorSortReference {
                key: key(ProvenanceRole::SortDeclaration, 0),
                sort: DescriptorSortRef::Declared(item("Expr", ItemKind::Sort)),
            },
            items: vec![
                DescriptorProductionItem::Terminal {
                    key: key(ProvenanceRole::BracketSyntaxItem, 0),
                    text: "(".into(),
                },
                DescriptorProductionItem::NonTerminal {
                    key: key(ProvenanceRole::BracketSyntaxItem, 1),
                    field_key: key(ProvenanceRole::BracketValueReference, 0),
                    declaration_key: None,
                    field: ProductionFieldId::new("value").unwrap(),
                    sort: Box::new(DescriptorSortReference {
                        key: key(ProvenanceRole::SortDeclaration, 0),
                        sort: DescriptorSortRef::Declared(expr_sort),
                    }),
                },
                DescriptorProductionItem::Terminal {
                    key: key(ProvenanceRole::BracketSyntaxItem, 2),
                    text: ")".into(),
                },
            ],
            attributes: vec![DescriptorProductionAttribute::Bracket {
                key: bracket_primary,
            }],
        }),
    );

    let subsort_primary = key(ProvenanceRole::SubsortDeclaration, 0);
    let subsort = grammar_descriptor(
        item("__subsort_Int_Value", ItemKind::Grammar),
        subsort_primary.clone(),
        &[
            key(ProvenanceRole::SubsortSubSort, 0),
            key(ProvenanceRole::SubsortSuperSort, 0),
        ],
        GrammarDescriptor::Subsort {
            key: subsort_primary,
            subsort: DescriptorSortReference {
                key: key(ProvenanceRole::SubsortSubSort, 0),
                sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
            },
            supersort: declared_sort(ProvenanceRole::SubsortSuperSort, 0, value_sort),
        },
    );

    let precedence_primary = key(ProvenanceRole::PrecedenceDeclaration, 0);
    let precedence = grammar_descriptor(
        item("__precedence_0", ItemKind::Grammar),
        precedence_primary.clone(),
        &[
            key(ProvenanceRole::PrecedenceChain, 0),
            key(ProvenanceRole::PrecedenceGroupReference, 0),
            key(ProvenanceRole::PrecedenceGroupReference, 1),
        ],
        GrammarDescriptor::Precedence {
            key: precedence_primary,
            chains: vec![DescriptorPrecedenceChain {
                key: key(ProvenanceRole::PrecedenceChain, 0),
                groups: vec![
                    DescriptorGroupReference {
                        key: key(ProvenanceRole::PrecedenceGroupReference, 0),
                        group: ProductionGroupId::new("multiplicative").unwrap(),
                    },
                    DescriptorGroupReference {
                        key: key(ProvenanceRole::PrecedenceGroupReference, 1),
                        group: ProductionGroupId::new("additive").unwrap(),
                    },
                ]
                .try_into()
                .unwrap(),
            }],
        },
    );

    let associativity_primary = key(ProvenanceRole::AssociativityDeclaration, 0);
    let associativity = grammar_descriptor(
        item("__associativity_0", ItemKind::Grammar),
        associativity_primary.clone(),
        &[
            key(ProvenanceRole::AssociativitySentence, 0),
            key(ProvenanceRole::AssociativityGroupReference, 0),
            key(ProvenanceRole::AssociativityGroupReference, 1),
        ],
        GrammarDescriptor::Associativity {
            key: associativity_primary,
            sentences: vec![DescriptorAssociativitySentence {
                key: key(ProvenanceRole::AssociativitySentence, 0),
                associativity: GroupAssociativity::Left,
                groups: vec![
                    DescriptorGroupReference {
                        key: key(ProvenanceRole::AssociativityGroupReference, 0),
                        group: ProductionGroupId::new("multiplicative").unwrap(),
                    },
                    DescriptorGroupReference {
                        key: key(ProvenanceRole::AssociativityGroupReference, 1),
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
        guarded_token.build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::InvalidProduction(
                GrammarProductionReason::NominalTokenRegexGuards
            )
        ))
    ));

    let mut regex_bracket = bracket.clone();
    expression_production(&mut regex_bracket).items[0] = DescriptorProductionItem::RegexTerminal {
        key: key(ProvenanceRole::BracketSyntaxItem, 0),
        precede_regex: None,
        regex: "[(]".into(),
        follow_regex: None,
    };
    assert!(matches!(
        regex_bracket.build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::InvalidProduction(GrammarProductionReason::BracketRegexItem)
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
        wrong_field_bracket.build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::InvalidProduction(GrammarProductionReason::BracketFieldName)
        ))
    ));

    let mut wrong_sort_bracket = bracket.clone();
    expression_production(&mut wrong_sort_bracket)
        .result_sort
        .sort = DescriptorSortRef::Declared(item("OtherExpr", ItemKind::Sort));
    assert!(matches!(
        wrong_sort_bracket.build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::InvalidProduction(
                GrammarProductionReason::BracketOwnerResultSortMismatch
            )
        ))
    ));

    let descriptors = vec![token, bracket, subsort, precedence, associativity];
    for descriptor in &descriptors {
        descriptor.build().unwrap();
    }
    let bundle = krs_ir::testing::descriptor_bundle(descriptors).unwrap();
    testing::assert_canonical_contract(&bundle);
    let json = bundle.to_canonical_json().unwrap();
    let decoded: DescriptorBundle = serde_json::from_str(&json).unwrap();
    assert_eq!(decoded.descriptors().len(), 5);
    assert!(json.contains("\"sort_source\": \"builtin\""));
    assert!(json.contains("\"grammar_kind\": \"precedence\""));
    assert!(json.contains("\"grammar_kind\": \"associativity\""));
}

#[test]
fn format_requires_explicit_constructor_syntax() {
    let mut descriptors = expression_descriptors();
    expression_production(&mut descriptors[0]).template_key = None;
    assert!(matches!(
        descriptors[0].build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::InvalidProduction(
                GrammarProductionReason::FormatWithoutConstructorSyntax
            )
        ))
    ));
}

#[test]
fn wrong_kinds_missing_origins_and_noncanonical_literals_are_rejected() {
    let mut descriptors = expression_descriptors();
    descriptors[0].id = item("wrong", ItemKind::Rule);
    assert!(matches!(
        descriptors[0].build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::DescriptorItemKind { .. }
        ))
    ));

    let mut descriptors = expression_descriptors();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptors[1].payload else {
        unreachable!()
    };
    rule.result = DescriptorTerm::Literal {
        key: key(ProvenanceRole::ClaimIdToken, 0),
        literal: DescriptorLiteral::Int("1_000".into()),
    };
    assert!(matches!(
        descriptors[1].build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::MissingProvenance(_)
        ))
    ));

    let mut descriptors = expression_descriptors();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptors[1].payload else {
        unreachable!()
    };
    rule.result = DescriptorTerm::Wildcard {
        key: key(ProvenanceRole::RuleLeftWildcard, 0),
    };
    assert!(matches!(
        descriptors[1].build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::InvalidTerm(_)
        ))
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
    string_key => (u8,),
    list_key => i64,
    set_key => i128,
    int_add_key => (u8, u8),
    int_sub_key => (u8, u16),
    int_mul_key => (u8, u32),
    int_tdiv_key => (u8, u64),
    int_mod_key => (u8, i8),
    int_pow_mod_key => (u8, i16),
    int_log2_key => (u8, i32),
    int_shift_right_key => (u8, i64),
    int_shift_left_key => (u16, i8),
    int_bit_and_key => (u16, i16),
    int_bit_xor_key => (u16, i32),
    int_bit_or_key => (u16, i64),
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
    bytes_empty_key => (i64, u32),
    bytes_update_key => (i64, u64),
    bytes_pad_right_key => (i128, u8),
    bytes_substring_key => (i128, u16),
    map_update_key => (u64, u64),
    map_get_key => (u64, i8),
    map_in_keys_key => (u64, i16),
    list_empty_key => (i8, u8),
    list_item_key => (i8, u16),
    list_concat_key => (i8, u32),
    list_get_key => (i8, u64),
    list_update_key => (i16, u8),
    list_size_key => (i16, u16),
    list_make_key => (i16, i32),
    list_range_key => (i16, u32),
    list_update_all_key => (i16, u64),
    set_empty_key => (i32, u8),
    set_item_key => (i32, u16),
    set_concat_key => (i32, u32),
    set_union_key => (i32, i64),
    set_contains_key => (i32, u64),
}

fn registry() -> HostBuiltinRegistry {
    let sorts = [
        HostTypeKey(k_sequence_key),
        HostTypeKey(int_key),
        HostTypeKey(bool_key),
        HostTypeKey(map_key),
        HostTypeKey(id_key),
        HostTypeKey(bytes_key),
        HostTypeKey(string_key),
        HostTypeKey(list_key),
        HostTypeKey(set_key),
    ];
    let operations = [
        HostTypeKey(int_add_key),
        HostTypeKey(int_sub_key),
        HostTypeKey(int_mul_key),
        HostTypeKey(int_tdiv_key),
        HostTypeKey(int_mod_key),
        HostTypeKey(int_pow_mod_key),
        HostTypeKey(int_log2_key),
        HostTypeKey(int_shift_right_key),
        HostTypeKey(int_shift_left_key),
        HostTypeKey(int_bit_and_key),
        HostTypeKey(int_bit_xor_key),
        HostTypeKey(int_bit_or_key),
        HostTypeKey(int_ge_key),
        HostTypeKey(int_gt_key),
        HostTypeKey(int_le_key),
        HostTypeKey(int_lt_key),
        HostTypeKey(int_eq_key),
        HostTypeKey(int_ne_key),
        HostTypeKey(bool_not_key),
        HostTypeKey(bool_eq_key),
        HostTypeKey(bool_ne_key),
        HostTypeKey(bool_and_key),
        HostTypeKey(bool_or_key),
        HostTypeKey(bytes_length_key),
        HostTypeKey(bytes_get_key),
        HostTypeKey(bytes_empty_key),
        HostTypeKey(bytes_update_key),
        HostTypeKey(bytes_pad_right_key),
        HostTypeKey(bytes_substring_key),
    ];
    let map_operations = [
        HostTypeKey(map_update_key),
        HostTypeKey(map_get_key),
        HostTypeKey(map_in_keys_key),
    ];
    let list_operations = [
        HostTypeKey(list_empty_key),
        HostTypeKey(list_item_key),
        HostTypeKey(list_concat_key),
        HostTypeKey(list_get_key),
        HostTypeKey(list_update_key),
        HostTypeKey(list_size_key),
        HostTypeKey(list_make_key),
        HostTypeKey(list_range_key),
        HostTypeKey(list_update_all_key),
    ];
    let set_operations = [
        HostTypeKey(set_empty_key),
        HostTypeKey(set_item_key),
        HostTypeKey(set_concat_key),
        HostTypeKey(set_union_key),
        HostTypeKey(set_contains_key),
    ];
    HostBuiltinRegistry {
        sorts,
        operations,
        map_operations,
        list_operations,
        set_operations,
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
        registry.resolve_operation(int_mod_key()),
        Some(BuiltinOperation::IntMod)
    );
    assert_eq!(
        registry.resolve_operation(int_pow_mod_key()),
        Some(BuiltinOperation::IntPowMod)
    );
    assert_eq!(
        registry.resolve_operation(int_shift_left_key()),
        Some(BuiltinOperation::IntShiftLeft)
    );
    assert_eq!(
        registry.resolve_operation(int_bit_xor_key()),
        Some(BuiltinOperation::IntBitXor)
    );
    assert_eq!(
        registry.resolve_map_operation(map_update_key()),
        Some(TermMapOperation::Update)
    );
    assert_eq!(
        registry.resolve_list_operation(list_get_key()),
        Some(ListOperation::Get)
    );
    assert_eq!(
        registry.resolve_list_operation(list_make_key()),
        Some(ListOperation::Make)
    );
    assert_eq!(
        registry.resolve_list_operation(list_range_key()),
        Some(ListOperation::Range)
    );
    assert_eq!(
        registry.resolve_list_operation(list_update_all_key()),
        Some(ListOperation::UpdateAll)
    );

    let mut collision = registry.clone();
    collision.operations[0] = HostTypeKey(int_key);
    assert_eq!(
        collision.validate(),
        Err(HostBuiltinRegistryError::ReusedRustType)
    );
    let mut map_collision = registry.clone();
    map_collision.map_operations[0] = HostTypeKey(int_key);
    assert_eq!(
        map_collision.validate(),
        Err(HostBuiltinRegistryError::ReusedRustType)
    );

    let mut list_collision = registry;
    list_collision.list_operations[0] = HostTypeKey(int_key);
    assert_eq!(
        list_collision.validate(),
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
    let json = krs_ir::testing::descriptor_bundle(expression_descriptors())
        .unwrap()
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
    *variable_key = key(ProvenanceRole::RuleResultType, 0);
    assert!(matches!(
        descriptors[1].build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::UnexpectedProvenance { .. }
        ))
    ));

    let mut descriptors = expression_descriptors();
    let primary = descriptors[0].provenance.primary_key().clone();
    let mut origins = descriptors[0].provenance.origins().to_vec();
    origins.push(DescriptorNodeOrigin::new(
        key(ProvenanceRole::ClaimIdToken, 0),
        origin(99),
    ));
    descriptors[0].provenance = DescriptorProvenance::new(primary, origins).unwrap();
    assert!(matches!(
        descriptors[0].build(),
        Err(krs_ir::DescriptorError::Grammar(
            GrammarTransportError::ExtraProvenance(_)
        ))
    ));
}

#[test]
fn grammar_argument_boundary_reports_context_free_mixed_forms() {
    let rule = expression_descriptors()
        .into_iter()
        .find_map(|descriptor| match descriptor.payload {
            DescriptorPayload::StructuredRule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    let original = serde_json::to_value(rule).unwrap();
    let expected = ArgumentsError::MixedForms;
    for field in ["subject", "result", "requires"] {
        for nested in [false, true] {
            for positional_first in [false, true] {
                let mut mixed = original["subject"].clone();
                let positional = serde_json::json!({
                    "argument_kind": "positional",
                    "value": mixed["arguments"][0]["value"].clone(),
                });
                mixed["arguments"][usize::from(!positional_first)] = positional;
                let mut term = original["subject"].clone();
                if nested {
                    term["arguments"][0]["value"] = mixed;
                } else {
                    term = mixed;
                }
                let mut json = original.clone();
                if field == "requires" {
                    json[field] = serde_json::json!({
                        "key": key(ProvenanceRole::RuleRequires, 0),
                        "term": term,
                    });
                } else {
                    json[field] = term;
                }
                assert!(
                    serde_json::from_value::<StructuredRuleDescriptor>(json)
                        .unwrap_err()
                        .to_string()
                        .starts_with(&expected.to_string())
                );
            }
        }
    }
}

#[test]
fn grammar_disjunction_boundary_reports_context_free_arity_error_with_location() {
    let rule = expression_descriptors()
        .into_iter()
        .find_map(|descriptor| match descriptor.payload {
            DescriptorPayload::StructuredRule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    let original = serde_json::to_value(rule).unwrap();
    for operands in 0..2 {
        let disjunction = serde_json::json!({
            "term_kind": "or_bool",
            "key": key(ProvenanceRole::ClaimOrBool, 0),
            "arguments": vec![original["subject"]["arguments"][0]["value"].clone(); operands],
        });
        let mut nested = original.clone();
        nested["subject"]["arguments"][0]["value"] = disjunction.clone();
        let mut cases = vec![nested];
        for field in ["subject", "result", "requires"] {
            let mut json = original.clone();
            json[field] = if field == "requires" {
                serde_json::json!({
                    "key": key(ProvenanceRole::RuleRequires, 0),
                    "term": disjunction,
                })
            } else {
                disjunction.clone()
            };
            cases.push(json);
        }
        for json in cases {
            let source = serde_json::to_string_pretty(&json).unwrap();
            let error = serde_json::from_str::<StructuredRuleDescriptor>(&source).unwrap_err();
            assert!(error.line() > 0);
            assert!(error.column() > 0);
            assert_eq!(
                error.to_string(),
                format!(
                    "or_bool requires at least two operands at line {} column {}",
                    error.line(),
                    error.column()
                )
            );
        }
    }
}
