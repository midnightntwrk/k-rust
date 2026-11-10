use super::*;
use crate::transport::detail::{
    StateCellContentReason, StateTermReason, TransportField, TransportItemKind,
};
use crate::transport::grammar::TermArgument;

use crate::{
    CellTermField, DescriptorApplicationRef, DescriptorApplicationReference, DescriptorLiteral,
    HostApplicationReference, HostApplicationTarget, HostTypeKey,
};

fn key(role: ProvenanceRole) -> ProvenanceKey {
    ProvenanceKey::new(role, 0)
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    crate::testing::item_in(
        crate::testing::package("TEST", "transport"),
        "terms",
        name,
        kind,
    )
}

fn host_type<T: 'static>() -> HostTypeReference {
    HostTypeReference {
        key: HostTypeKey(std::any::TypeId::of::<T>),
        authored_path: std::any::type_name::<T>().into(),
    }
}

fn descriptor_sort(role: ProvenanceRole, kind: ItemKind) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(role),
        sort: DescriptorSortRef::Declared(item("Target", kind)),
    }
}

fn host_sort(role: ProvenanceRole) -> HostSortReference {
    HostSortReference {
        key: key(role),
        target: host_type::<()>(),
    }
}

fn check_term<S: ValidationStage>(term: &Term<S>) -> Result<(), StateTransportError> {
    validate_rule_term(
        term,
        ValidationSide::Left,
        &[],
        &mut Vec::new(),
        &mut RuleWalk::default(),
        &mut WireKeys::default(),
    )
}

#[test]
fn claim_binders_validate_descriptor_sort_after_its_provenance() {
    let descriptor: ClaimBinder<DescriptorStage> = ClaimBinder {
        declaration_key: key(ProvenanceRole::ClaimUniversalBinder),
        name_key: key(ProvenanceRole::ClaimBinderName),
        name: "value".into(),
        sort: descriptor_sort(ProvenanceRole::ClaimBinderSort, ItemKind::Constructor),
    };
    let host: ClaimBinder<HostStage> = ClaimBinder {
        declaration_key: descriptor.declaration_key.clone(),
        name_key: descriptor.name_key.clone(),
        name: descriptor.name.clone(),
        sort: host_sort(ProvenanceRole::ClaimBinderSort),
    };
    let descriptor_catalog = [ProtocolRuleBinding {
        name: "value".into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: descriptor.sort.clone(),
        },
    }];
    let host_catalog = [ProtocolRuleBinding {
        name: "value".into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: host.sort.clone(),
        },
    }];
    assert_eq!(
        validate_rule_claim_binders::<DescriptorStage>(
            std::slice::from_ref(&descriptor),
            &descriptor_catalog,
            ProvenanceRole::ClaimUniversalBinder,
            &mut WireKeys::default()
        ),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidClaimBinderSort
        ))
    );
    assert!(
        validate_rule_claim_binders::<HostStage>(
            &[host],
            &host_catalog,
            ProvenanceRole::ClaimUniversalBinder,
            &mut WireKeys::default()
        )
        .is_ok()
    );
    let mut malformed = descriptor;
    malformed.sort.key = key(ProvenanceRole::RuleBindingType);
    assert_eq!(
        validate_rule_claim_binders::<DescriptorStage>(
            &[malformed],
            &descriptor_catalog,
            ProvenanceRole::ClaimUniversalBinder,
            &mut WireKeys::default()
        ),
        Err(StateTransportError::UnexpectedProvenance {
            expected: ProvenanceRole::ClaimBinderSort,
            actual: key(ProvenanceRole::RuleBindingType),
        })
    );
}

#[test]
fn rule_binding_catalog_preserves_descriptor_only_declared_sort_check() {
    let descriptor = [ProtocolRuleBinding {
        name: "value".into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: descriptor_sort(ProvenanceRole::RuleBindingType, ItemKind::Constructor),
        },
    }];
    let host = [ProtocolRuleBinding {
        name: "value".into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: host_sort(ProvenanceRole::RuleBindingType),
        },
    }];
    assert_eq!(
        validate_rule_binding_catalog::<DescriptorStage>(&descriptor, &mut WireKeys::default()),
        Err(StateTransportError::ItemKind {
            field: TransportField::RuleBindingSort,
            expected: TransportItemKind::Sort,
            actual: ItemKind::Constructor,
        })
    );
    assert!(validate_rule_binding_catalog::<HostStage>(&host, &mut WireKeys::default()).is_ok());
}

#[test]
fn rule_applications_preserve_reference_check_and_path_error_order() {
    let mut descriptor: Term<DescriptorStage> = Term::Application {
        instance: Vec::new(),
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: DescriptorApplicationReference {
            key: key(ProvenanceRole::RuleLeftApplicationHead),
            application: DescriptorApplicationRef::Declared(item("Target", ItemKind::Sort)),
        },
        path_key: key(ProvenanceRole::RuleLeftApplicationHead),
        arguments: crate::Arguments::default(),
        update: None,
        open: false,
    };
    let host: Term<HostStage> = Term::Application {
        instance: Vec::new(),
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: HostApplicationReference {
            key: key(ProvenanceRole::RuleLeftApplicationHead),
            target: HostApplicationTarget::Nominal(host_type::<()>()),
        },
        path_key: key(ProvenanceRole::RuleLeftApplicationHead),
        arguments: crate::Arguments::default(),
        update: None,
        open: false,
    };
    assert_eq!(
        check_term(&descriptor),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidApplicationTarget
        ))
    );
    assert!(check_term(&host).is_ok());
    if let Term::Application { path_key, .. } = &mut descriptor {
        *path_key = key(ProvenanceRole::RuleLeftReference);
    }
    assert_eq!(
        check_term(&descriptor),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::RuleTermKeyMismatch
        ))
    );
}

fn assert_named_argument_order<S: ValidationStage>(reference: S::Application) {
    let field = ProductionFieldId::new("value").unwrap();
    let mut term: Term<S> = Term::Application {
        instance: Vec::new(),
        head_class: DescriptorApplicationHeadClass::Applied,
        path_key: key(ProvenanceRole::RuleLeftApplicationHead),
        reference,
        arguments: vec![
            TermArgument::Named {
                key: key(ProvenanceRole::RuleLeftRecordFieldName),
                field: field.clone(),
                value: Box::new(Term::Literal {
                    key: key(ProvenanceRole::RuleLeftLiteral),
                    literal: DescriptorLiteral::Bool(true),
                }),
            },
            TermArgument::Named {
                key: key(ProvenanceRole::RuleLeftLiteral),
                field,
                value: Box::new(Term::Variable {
                    key: key(ProvenanceRole::RuleLeftReference),
                    path_key: key(ProvenanceRole::RuleLeftReference),
                    name: "undeclared".to_owned(),
                }),
            },
        ]
        .try_into()
        .unwrap(),
        update: None,
        open: false,
    };
    assert_eq!(
        check_term(&term),
        Err(StateTransportError::DuplicateValue(
            TransportField::RuleApplicationRecordFields
        )),
    );
    if let Term::Application { arguments, .. } = &mut term
        && let crate::Arguments::Named(arguments) = arguments
    {
        *arguments.first_mut().value = Term::Literal {
            key: key(ProvenanceRole::RuleLeftLiteral),
            literal: DescriptorLiteral::Int("-0".to_owned()),
        };
    }
    assert_eq!(
        check_term(&term),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::NonCanonicalIntegerLiteral
        )),
    );
}

#[test]
fn rule_named_arguments_preserve_duplicate_before_provenance_and_preorder() {
    assert_named_argument_order::<DescriptorStage>(DescriptorApplicationReference {
        key: key(ProvenanceRole::RuleLeftApplicationHead),
        application: DescriptorApplicationRef::Declared(item("Target", ItemKind::Constructor)),
    });
    assert_named_argument_order::<HostStage>(HostApplicationReference {
        key: key(ProvenanceRole::RuleLeftApplicationHead),
        target: HostApplicationTarget::Nominal(host_type::<()>()),
    });
}

#[test]
fn anonymous_terms_validate_descriptor_sort_before_provenance() {
    let descriptor: Term<DescriptorStage> = Term::Anonymous {
        key: key(ProvenanceRole::RuleLeftLiteral),
        sort: descriptor_sort(ProvenanceRole::ClaimAnonymousSort, ItemKind::Constructor),
        spelling_key: key(ProvenanceRole::ClaimAnonymousSpelling),
        spelling: "_value".into(),
    };
    let mut host: Term<HostStage> = Term::Anonymous {
        key: key(ProvenanceRole::ClaimAnonymous),
        sort: host_sort(ProvenanceRole::ClaimAnonymousSort),
        spelling_key: key(ProvenanceRole::ClaimAnonymousSpelling),
        spelling: "_value".into(),
    };
    assert_eq!(
        check_term(&descriptor),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidAnonymousSort
        ))
    );
    assert!(check_term(&host).is_ok());
    // The spelling is a node of its own, keyed by its role.
    let mut spelled = host.clone();
    if let Term::Anonymous { spelling_key, .. } = &mut spelled {
        *spelling_key = key(ProvenanceRole::ClaimAnonymous);
    }
    assert_eq!(
        check_term(&spelled),
        Err(StateTransportError::UnexpectedProvenance {
            expected: ProvenanceRole::ClaimAnonymousSpelling,
            actual: key(ProvenanceRole::ClaimAnonymous),
        })
    );
    if let Term::Anonymous {
        key: occurrence_key,
        ..
    } = &mut host
    {
        *occurrence_key = key(ProvenanceRole::RuleLeftLiteral);
    }
    assert_eq!(
        check_term(&host),
        Err(StateTransportError::UnexpectedProvenance {
            expected: ProvenanceRole::ClaimAnonymous,
            actual: key(ProvenanceRole::RuleLeftLiteral),
        })
    );
}

#[test]
fn fragments_preserve_stage_specific_declaration_and_empty_errors() {
    let mut descriptor: Term<DescriptorStage> = Term::Cell {
        key: key(ProvenanceRole::RuleLeftApplicationHead),
        path_key: key(ProvenanceRole::RuleLeftApplicationHead),
        declaration: item("Target", ItemKind::Sort),
        fields: Vec::new(),
        open: false,
        update: None,
    };
    let mut host: Term<HostStage> = Term::Cell {
        key: key(ProvenanceRole::RuleLeftApplicationHead),
        path_key: key(ProvenanceRole::RuleLeftApplicationHead),
        declaration: host_type::<()>(),
        fields: Vec::new(),
        open: false,
        update: None,
    };
    assert_eq!(
        check_term(&descriptor),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::EmptyOrNonNominalFragment
        ))
    );
    assert_eq!(
        check_term(&host),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::EmptyFragment
        ))
    );
    let field = || CellTermField {
        key: key(ProvenanceRole::RuleLeftRecordFieldName),
        field: ProductionFieldId::new("value").unwrap(),
        value: Box::new(Term::Literal {
            key: key(ProvenanceRole::RuleLeftLiteral),
            literal: DescriptorLiteral::Bool(true),
        }),
    };
    if let Term::Cell { fields, .. } = &mut descriptor {
        fields.push(field());
    }
    if let Term::Cell { fields, .. } = &mut host {
        fields.push(CellTermField {
            key: key(ProvenanceRole::RuleLeftRecordFieldName),
            field: ProductionFieldId::new("value").unwrap(),
            value: Box::new(Term::Literal {
                key: key(ProvenanceRole::RuleLeftLiteral),
                literal: DescriptorLiteral::Bool(true),
            }),
        });
    }
    assert_eq!(
        check_term(&descriptor),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::EmptyOrNonNominalFragment
        ))
    );
    assert!(check_term(&host).is_ok());
    // In a cell value, a fragment's path names its head's node, as an
    // application's does.
    if let Term::Cell { path_key, .. } = &mut host {
        *path_key = key(ProvenanceRole::RuleLeftPath);
    }
    assert_eq!(
        check_term(&host),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::RuleTermKeyMismatch
        ))
    );
}

fn cells<S: ValidationStage>(reference: S::Cell) -> ProtocolRuleCells<S::Cell, Term<S>> {
    ProtocolRuleCells {
        key: key(ProvenanceRole::RuleLeftCellsPayload),
        cells: vec![ProtocolRuleCell {
            field: reference,
            wrapper_key: Some(key(ProvenanceRole::RuleLeftCellsWrapper)),
            wrapper: Some(CellWrapper::Cell),
            value: ProtocolRuleStateTerm::Term(Term::Literal {
                key: key(ProvenanceRole::RuleLeftLiteral),
                literal: DescriptorLiteral::Bool(true),
            }),
        }],
        remainder: ProtocolRuleFrame::Exact,
    }
}

#[test]
fn selected_cells_preserve_descriptor_identity_and_owner_checks() {
    let owner = DescriptorConfigurationReference {
        key: key(ProvenanceRole::RuleType),
        configuration: item("Config", ItemKind::Configuration),
        subject: None,
    };
    let descriptor = |kind| {
        cells::<DescriptorStage>(DescriptorCellReference {
            key: key(ProvenanceRole::RuleLeftCellsField),
            cell: crate::DescriptorCellIdentity {
                owner: item("Foreign", kind),
                field: "value".into(),
            },
        })
    };
    let host_owner = HostConfigurationReference {
        key: owner.key.clone(),
        configuration: host_type::<()>(),
    };
    let host = cells::<HostStage>(HostCellReference {
        key: key(ProvenanceRole::RuleLeftCellsField),
        cell: crate::HostCellIdentity {
            owner: host_type::<bool>().key,
            field: host_type::<u8>().key,
        },
    });
    assert_eq!(
        validate_rule_cells::<DescriptorStage>(
            &descriptor(ItemKind::Configuration),
            &owner,
            RuleSide::Left,
            &[],
            &mut Vec::new(),
            &mut RuleWalk::default(),
            &mut WireKeys::default()
        ),
        Err(StateTransportError::CellOwnerMismatch)
    );
    assert!(
        validate_rule_cells::<DescriptorStage>(
            &descriptor(ItemKind::Cell),
            &owner,
            RuleSide::Left,
            &[],
            &mut Vec::new(),
            &mut RuleWalk::default(),
            &mut WireKeys::default()
        )
        .is_ok()
    );
    assert!(
        validate_rule_cells::<HostStage>(
            &host,
            &host_owner,
            RuleSide::Left,
            &[],
            &mut Vec::new(),
            &mut RuleWalk::default(),
            &mut WireKeys::default()
        )
        .is_ok()
    );
    assert_eq!(
        validate_rule_cells::<DescriptorStage>(
            &descriptor(ItemKind::Sort),
            &owner,
            RuleSide::Left,
            &[],
            &mut Vec::new(),
            &mut RuleWalk::default(),
            &mut WireKeys::default()
        ),
        Err(StateTransportError::ItemKind {
            field: TransportField::CellIdentityOwner,
            expected: TransportItemKind::ConfigurationOrCell,
            actual: ItemKind::Sort,
        })
    );
}

fn assert_duplicate_selected_cells<S: RuleValidationStage>(
    reference: S::Cell,
    owner: &S::Configuration,
) {
    let mut payload = cells::<S>(reference);
    payload.cells.push(payload.cells[0].clone());
    assert_eq!(
        validate_rule_cells::<S>(
            &payload,
            owner,
            RuleSide::Left,
            &[],
            &mut Vec::new(),
            &mut RuleWalk::default(),
            &mut WireKeys::default(),
        ),
        Err(StateTransportError::DuplicateValue(
            TransportField::SelectedRuleCells
        )),
    );
}

#[test]
fn duplicate_selected_cells_use_stage_identities_before_second_cell_provenance() {
    let configuration = item("Config", ItemKind::Configuration);
    assert_duplicate_selected_cells::<DescriptorStage>(
        DescriptorCellReference {
            key: key(ProvenanceRole::RuleLeftCellsField),
            cell: crate::DescriptorCellIdentity {
                owner: configuration.clone(),
                field: "value".into(),
            },
        },
        &DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleType),
            configuration,
            subject: None,
        },
    );
    assert_duplicate_selected_cells::<HostStage>(
        HostCellReference {
            key: key(ProvenanceRole::RuleLeftCellsField),
            cell: crate::HostCellIdentity {
                owner: host_type::<()>().key,
                field: host_type::<u8>().key,
            },
        },
        &HostConfigurationReference {
            key: key(ProvenanceRole::RuleType),
            configuration: host_type::<()>(),
        },
    );
}

fn alias<S: ValidationStage>(configuration: S::Configuration) -> ContextAlias<S> {
    ContextAlias {
        declaration_key: key(ProvenanceRole::ContextAliasDeclaration),
        name_key: key(ProvenanceRole::ContextAliasName),
        here_key: key(ProvenanceRole::ContextAliasHere),
        name: "context".into(),
        here: "HERE".into(),
        pattern_key: key(ProvenanceRole::RulePattern),
        configuration,
        bindings: vec![ProtocolContextAliasBinding {
            name: "HERE".into(),
            kind: ProtocolContextAliasBindingKind::Here,
        }],
        pattern: ProtocolRuleCells {
            key: key(ProvenanceRole::RuleLeftCellsPayload),
            cells: Vec::new(),
            remainder: ProtocolRuleFrame::Exact,
        },
        result: None,
    }
}

#[test]
fn context_aliases_preserve_stage_specific_early_checks() {
    let descriptor = alias::<DescriptorStage>(DescriptorConfigurationReference {
        key: key(ProvenanceRole::RuleType),
        configuration: item("Config", ItemKind::Configuration),
        subject: None,
    });
    let host = alias::<HostStage>(HostConfigurationReference {
        key: key(ProvenanceRole::RuleType),
        configuration: host_type::<()>(),
    });
    assert_eq!(
        descriptor.validate(ItemKind::ContextAlias),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::AliasHereContentOccurrence
        ))
    );
    assert!(host.validate(ItemKind::ContextAlias).is_ok());
    let mut duplicate_descriptor = descriptor.clone();
    duplicate_descriptor
        .bindings
        .push(duplicate_descriptor.bindings[0].clone());
    let mut duplicate_host = host.clone();
    duplicate_host
        .bindings
        .push(duplicate_host.bindings[0].clone());
    assert_eq!(
        duplicate_descriptor.validate(ItemKind::ContextAlias),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::DuplicateAliasBinding
        ))
    );
    assert_eq!(
        duplicate_host.validate(ItemKind::ContextAlias),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::AliasHereBindingCount
        ))
    );
    let mut wrong_kind = descriptor;
    wrong_kind.configuration.configuration = item("Sort", ItemKind::Sort);
    wrong_kind.name.clear();
    assert_eq!(
        wrong_kind.validate(ItemKind::ContextAlias),
        Err(StateTransportError::ItemKind {
            field: TransportField::ConfigurationRuleType,
            expected: TransportItemKind::Configuration,
            actual: ItemKind::Sort,
        })
    );
}

#[test]
fn ordinary_alias_duplicates_preserve_distinct_stage_errors() {
    let mut descriptor = alias::<DescriptorStage>(DescriptorConfigurationReference {
        key: key(ProvenanceRole::RuleType),
        configuration: item("Config", ItemKind::Configuration),
        subject: None,
    });
    let mut host = alias::<HostStage>(HostConfigurationReference {
        key: key(ProvenanceRole::RuleType),
        configuration: host_type::<()>(),
    });
    for _ in 0..2 {
        descriptor.bindings.push(ProtocolContextAliasBinding {
            name: "value".to_owned(),
            kind: ProtocolContextAliasBindingKind::Term {
                sort: descriptor_sort(ProvenanceRole::RuleBindingType, ItemKind::Sort),
            },
        });
        host.bindings.push(ProtocolContextAliasBinding {
            name: "value".to_owned(),
            kind: ProtocolContextAliasBindingKind::Term {
                sort: host_sort(ProvenanceRole::RuleBindingType),
            },
        });
    }
    assert_eq!(
        descriptor.validate(ItemKind::ContextAlias),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::DuplicateAliasBinding
        )),
    );
    assert_eq!(
        host.validate(ItemKind::ContextAlias),
        Err(StateTransportError::DuplicateValue(
            TransportField::ContextAliasBindings
        )),
    );
    descriptor.bindings.remove(0);
    host.bindings.remove(0);
    assert_eq!(
        descriptor.validate(ItemKind::ContextAlias),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::DuplicateAliasBinding
        )),
    );
    assert_eq!(
        host.validate(ItemKind::ContextAlias),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::AliasHereBindingCount
        )),
    );
}

fn empty_rule<S: RuleValidationStage>(
    subject_configuration: S::Configuration,
    result_configuration: S::Configuration,
) -> ConfigurationRule<S> {
    ConfigurationRule {
        sentence_kind: crate::ConfigurationSentenceKind::Transition,
        label: Some(DescriptorRuleLabel {
            key: key(ProvenanceRole::RuleLabel),
            name: "step".into(),
        }),
        priority: None,
        nondet: None,
        skipped_operand: None,
        requires: None,
        claim: None,
        pattern_key: key(ProvenanceRole::RulePattern),
        subject_configuration,
        result_key: Some(key(ProvenanceRole::RuleResult)),
        result_configuration: Some(result_configuration),
        bindings: Vec::new(),
        subject: ProtocolRuleCells {
            key: key(ProvenanceRole::RuleLeftCellsPayload),
            cells: Vec::new(),
            remainder: ProtocolRuleFrame::Exact,
        },
        result: Some(ProtocolRuleCells {
            key: key(ProvenanceRole::RuleRightCellsPayload),
            cells: Vec::new(),
            remainder: ProtocolRuleFrame::Exact,
        }),
        existentials: Vec::new(),
        ensures: None,
        fresh: Vec::new(),
        evaluation: None,
    }
}

#[test]
fn rule_key_collection_preserves_stage_specific_label_and_declaration_ownership() {
    let descriptor = empty_rule::<DescriptorStage>(
        DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleType),
            configuration: item("Config", ItemKind::Configuration),
            subject: None,
        },
        DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleResultType),
            configuration: item("Config", ItemKind::Configuration),
            subject: None,
        },
    );
    let host = empty_rule::<HostStage>(
        HostConfigurationReference {
            key: key(ProvenanceRole::RuleType),
            configuration: host_type::<()>(),
        },
        HostConfigurationReference {
            key: key(ProvenanceRole::RuleResultType),
            configuration: host_type::<()>(),
        },
    );
    let mut descriptor_keys = WireKeys::default();
    let mut host_keys = WireKeys::default();
    validate_configuration_rule(&descriptor, ItemKind::Rule, &mut descriptor_keys).unwrap();
    validate_configuration_rule(&host, ItemKind::Rule, &mut host_keys).unwrap();
    let (descriptor_keys, host_keys) = (descriptor_keys.into_defined(), host_keys.into_defined());
    assert_eq!(
        descriptor_keys
            .difference(&host_keys)
            .cloned()
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([
            key(ProvenanceRole::RuleLabel),
            key(ProvenanceRole::RuleDeclaration),
        ])
    );
    assert!(host_keys.is_subset(&descriptor_keys));
}

#[test]
fn configuration_rules_compare_stable_ids_and_resolved_host_aliases() {
    type ConfigAlias = ();
    let mut descriptor = empty_rule::<DescriptorStage>(
        DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleType),
            configuration: item("Config", ItemKind::Configuration),
            subject: None,
        },
        DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleResultType),
            configuration: item("Other", ItemKind::Configuration),
            subject: None,
        },
    );
    let mut host = empty_rule::<HostStage>(
        HostConfigurationReference {
            key: key(ProvenanceRole::RuleType),
            configuration: host_type::<()>(),
        },
        HostConfigurationReference {
            key: key(ProvenanceRole::RuleResultType),
            configuration: host_type::<ConfigAlias>(),
        },
    );
    host.result_configuration
        .as_mut()
        .unwrap()
        .configuration
        .authored_path = "ConfigAlias".to_owned();
    assert_eq!(host.validate(ItemKind::Rule), Ok(()));
    let mismatch = Err(StateTransportError::InvalidCellContent(
        StateCellContentReason::RuleSubjectAndResultConfigurationsDiffer,
    ));
    assert_eq!(descriptor.validate(ItemKind::Rule), mismatch);
    descriptor
        .result_configuration
        .as_mut()
        .unwrap()
        .configuration = descriptor.subject_configuration.configuration.clone();
    assert_eq!(descriptor.validate(ItemKind::Rule), Ok(()));
    host.result_configuration.as_mut().unwrap().configuration = host_type::<bool>();
    assert_eq!(host.validate(ItemKind::Rule), mismatch);
}

/// A rule about a cell group keeps one subject on both sides, names only
/// group cells, and is never a claim.
#[test]
fn group_subjects_match_name_group_cells_and_refuse_claims() {
    let group = |name| crate::DescriptorSubject::Group {
        declaration: item(name, ItemKind::Cell),
    };
    let reference = |role, subject| DescriptorConfigurationReference {
        key: key(role),
        configuration: item("Config", ItemKind::Configuration),
        subject,
    };
    let rule = |subject, result| {
        empty_rule::<DescriptorStage>(
            reference(ProvenanceRole::RuleType, subject),
            reference(ProvenanceRole::RuleResultType, result),
        )
    };
    assert_eq!(
        rule(Some(group("Cpu")), Some(group("Cpu"))).validate(ItemKind::Rule),
        Ok(())
    );
    let mismatch = Err(StateTransportError::InvalidCellContent(
        StateCellContentReason::RuleSubjectAndResultConfigurationsDiffer,
    ));
    assert_eq!(
        rule(Some(group("Cpu")), None).validate(ItemKind::Rule),
        mismatch
    );
    assert_eq!(
        rule(Some(group("Cpu")), Some(group("Timer"))).validate(ItemKind::Rule),
        mismatch
    );
    assert_eq!(
        rule(
            Some(crate::DescriptorSubject::Group {
                declaration: item("Config", ItemKind::Configuration),
            }),
            None,
        )
        .validate(ItemKind::Rule),
        Err(StateTransportError::ItemKind {
            field: TransportField::RuleSubjectGroup,
            expected: TransportItemKind::Cell,
            actual: ItemKind::Configuration,
        })
    );

    let mut claim = rule(Some(group("Cpu")), Some(group("Cpu")));
    claim.sentence_kind = crate::ConfigurationSentenceKind::Claim;
    claim.claim = Some(Claim {
        declaration_key: key(ProvenanceRole::ClaimDeclaration),
        modality_key: key(ProvenanceRole::ClaimModality),
        modality: ClaimModality::OnePath,
        circularity_key: None,
        trusted_key: None,
        universals: Vec::new(),
        existentials: Vec::new(),
        ensures: None,
        or_bool_keys: Vec::new(),
        pattern: None,
    });
    assert_eq!(
        claim.validate(ItemKind::Claim),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::GroupSubjectClaim
        ))
    );

    let cell = |owner| DescriptorCellReference {
        key: key(ProvenanceRole::RuleLeftCellsField),
        cell: crate::DescriptorCellIdentity {
            owner,
            field: "value".into(),
        },
    };
    let whole = reference(ProvenanceRole::RuleType, None);
    let part = reference(ProvenanceRole::RuleType, Some(group("Cpu")));
    let own = cell(item("Config", ItemKind::Configuration));
    let grouped = cell(item("Cpu", ItemKind::Cell));
    assert_eq!(DescriptorStage::validate_rule_cell(&own, &whole), Ok(()));
    assert_eq!(
        DescriptorStage::validate_rule_cell(&grouped, &whole),
        Ok(())
    );
    assert_eq!(DescriptorStage::validate_rule_cell(&grouped, &part), Ok(()));
    assert_eq!(
        DescriptorStage::validate_rule_cell(&own, &part),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::CellOutsideGroupSubject
        ))
    );
    assert_eq!(
        DescriptorStage::validate_rule_cell(&cell(item("Other", ItemKind::Configuration)), &part),
        Err(StateTransportError::CellOwnerMismatch)
    );
}

/// An equation's function context keys its cells as a rule's left side:
/// each key has its role, and one node defines it.
#[test]
fn function_context_cells_have_their_roles_and_one_definition() {
    let configuration = item("Config", ItemKind::Configuration);
    let context = |cells| DescriptorFunctionContext {
        key: key(ProvenanceRole::FunctionContext),
        configuration: DescriptorConfigurationReference {
            key: key(ProvenanceRole::FunctionContextType),
            configuration: configuration.clone(),
            subject: None,
        },
        bindings: Vec::new(),
        cells,
    };
    let cells = cells::<DescriptorStage>(DescriptorCellReference {
        key: key(ProvenanceRole::RuleLeftCellsField),
        cell: crate::DescriptorCellIdentity {
            owner: configuration.clone(),
            field: "value".into(),
        },
    });
    let mut keys = WireKeys::default();
    context(cells.clone()).collect_keys(&mut keys).unwrap();
    assert_eq!(keys.defined().len(), 6);

    let mut misplaced = cells.clone();
    misplaced.cells[0].wrapper_key = Some(key(ProvenanceRole::RuleRightCellsWrapper));
    assert_eq!(
        context(misplaced).collect_keys(&mut WireKeys::default()),
        Err(crate::GrammarTransportError::UnexpectedProvenance {
            expected: ProvenanceRole::RuleLeftCellsWrapper,
            actual: key(ProvenanceRole::RuleRightCellsWrapper),
        })
    );
    let mut repeated = cells;
    repeated.cells.push(repeated.cells[0].clone());
    assert_eq!(
        context(repeated).collect_keys(&mut WireKeys::default()),
        Err(crate::GrammarTransportError::DuplicateProvenance(key(
            ProvenanceRole::RuleLeftCellsField
        )))
    );
}

/// The name `name` in a left side.
fn reference<S: ValidationStage>(name: &str, ordinal: u32) -> Term<S> {
    let key = ProvenanceKey::new(ProvenanceRole::RuleLeftReference, ordinal);
    Term::Variable {
        key: key.clone(),
        path_key: key,
        name: name.to_owned(),
    }
}

/// `{ let y = x; y }`, under keys of its own for each `ordinal`.
fn block<S: ValidationStage>(ordinal: u32) -> Term<S> {
    Term::Let {
        key: ProvenanceKey::new(ProvenanceRole::Let, ordinal),
        pattern: Box::new(reference("y", ordinal * 10 + 1)),
        sort: None,
        value: Box::new(reference("x", ordinal * 10 + 2)),
        body: Box::new(reference("y", ordinal * 10 + 3)),
    }
}

/// `reference(argument)` in a left side.
fn applied<S: ValidationStage>(reference: S::Application, argument: Term<S>) -> Term<S> {
    Term::Application {
        instance: Vec::new(),
        head_class: DescriptorApplicationHeadClass::Applied,
        reference,
        path_key: key(ProvenanceRole::RuleLeftApplicationHead),
        arguments: crate::Arguments::Positional(vec![Box::new(argument)]),
        update: None,
        open: false,
    }
}

/// Validates `term` as a left side over `bindings`.
fn check<S: ValidationStage>(
    term: &Term<S>,
    bindings: &[ProtocolRuleBinding<S::Sort>],
) -> Result<(), StateTransportError> {
    validate_rule_term(
        term,
        ValidationSide::Left,
        bindings,
        &mut Vec::new(),
        &mut RuleWalk::default(),
        &mut WireKeys::default(),
    )
}

/// A set's element in a left side is read as a key: the walk admits a `let` block there, which
/// the position table and the compiler judge, and keeps refusing one inside a local pattern within
/// the element and in a field of any other application. A host occurrence is told by its authored
/// path, a descriptor occurrence by its resolved operation.
#[test]
fn a_set_s_element_admits_a_let_block_outside_its_local_patterns() {
    let descriptor = |application: DescriptorApplicationRef| DescriptorApplicationReference {
        key: key(ProvenanceRole::RuleLeftApplicationHead),
        application,
    };
    let singleton = || descriptor(DescriptorApplicationRef::Set(crate::SetOperation::Item));
    let constructor = || {
        descriptor(DescriptorApplicationRef::Declared(item(
            "Wrap",
            ItemKind::Constructor,
        )))
    };
    let host = |path: &'static str| HostApplicationReference {
        key: key(ProvenanceRole::RuleLeftApplicationHead),
        target: HostApplicationTarget::Nominal(HostTypeReference {
            key: HostTypeKey(std::any::TypeId::of::<()>),
            authored_path: path.into(),
        }),
    };
    // `x` is the rule's binding; `y` is the block's.
    let descriptor_bindings = [ProtocolRuleBinding {
        name: "x".into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: descriptor_sort(ProvenanceRole::RuleBindingType, ItemKind::Sort),
        },
    }];
    let host_bindings = [ProtocolRuleBinding {
        name: "x".into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: host_sort(ProvenanceRole::RuleBindingType),
        },
    }];
    let check_descriptor = |term: Term<DescriptorStage>| check(&term, &descriptor_bindings);
    let check_host = |term: Term<HostStage>| check(&term, &host_bindings);
    let refused = Err(StateTransportError::InvalidTerm(
        StateTermReason::LetInPattern,
    ));
    assert_eq!(
        check_descriptor(applied::<DescriptorStage>(singleton(), block(1))),
        Ok(())
    );
    assert_eq!(
        check_descriptor(applied::<DescriptorStage>(constructor(), block(1))),
        refused
    );
    // A `let` block inside a test's pattern within the element is a pattern's, not the element's.
    let test = |ordinal| Term::Matches {
        key: ProvenanceKey::new(ProvenanceRole::Matches, ordinal),
        subject: Box::new(reference("x", ordinal * 10 + 4)),
        pattern: Box::new(block(ordinal)),
    };
    assert_eq!(
        check_descriptor(applied::<DescriptorStage>(singleton(), test(2))),
        refused
    );
    assert_eq!(
        check_host(applied::<HostStage>(
            host("k::builtin::set::item"),
            block(1)
        )),
        Ok(())
    );
    assert_eq!(
        check_host(applied::<HostStage>(host("set::item"), block(1))),
        Ok(())
    );
    // Another spelling of the singleton reads its element as a field (finding NT-31-1).
    assert_eq!(
        check_host(applied::<HostStage>(host("item"), block(1))),
        refused
    );
}

/// A rule term keyed `role`, ordinal `ordinal`: the literal `true`.
fn list_literal(role: ProvenanceRole, ordinal: u32) -> Term<DescriptorStage> {
    Term::Literal {
        key: ProvenanceKey::new(role, ordinal),
        literal: DescriptorLiteral::Bool(true),
    }
}

/// One level of list notation on `side`, `[element, ..rest]` or `[..rest, element]`.
fn list_level(
    side: ValidationSide,
    notation: crate::ListNotation,
    element: Term<DescriptorStage>,
    rest: Term<DescriptorStage>,
    ordinal: u32,
) -> Term<DescriptorStage> {
    let role = match side {
        ValidationSide::Left => ProvenanceRole::RuleLeftApplicationHead,
        _ => ProvenanceRole::RuleRightApplicationHead,
    };
    let head = ProvenanceKey::new(role, ordinal);
    let arguments = match notation {
        crate::ListNotation::Snoc => vec![rest, element],
        _ => vec![element, rest],
    };
    Term::Application {
        instance: Vec::new(),
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: DescriptorApplicationReference {
            key: head.clone(),
            application: DescriptorApplicationRef::ListNotation(notation),
        },
        path_key: head,
        arguments: crate::Arguments::Positional(arguments.into_iter().map(Box::new).collect()),
        update: None,
        open: false,
    }
}

/// The unnamed rest of a list, keyed as the `..` it is on `side`.
fn kept_rest(side: ValidationSide, ordinal: u32) -> Term<DescriptorStage> {
    let role = match side {
        ValidationSide::Left => ProvenanceRole::RuleLeftWildcard,
        _ => ProvenanceRole::RuleRightWildcard,
    };
    Term::KeptRest {
        key: ProvenanceKey::new(role, ordinal),
    }
}

/// A list cell entry's state validated on `side`, as the entry's root when `entry_root`, in a
/// sentence with a result when `with_result`.
fn list_entry(
    state: &ProtocolRuleStateTerm<Term<DescriptorStage>>,
    side: RuleSide,
    entry_root: bool,
    with_result: bool,
) -> Result<(), StateTransportError> {
    validate_rule_state::<DescriptorStage>(
        state,
        side,
        &[],
        &mut Vec::new(),
        &mut RuleWalk {
            kept_rests: with_result,
            ..RuleWalk::default()
        },
        &mut WireKeys::default(),
        entry_root,
    )
}

const OUTSIDE_LIST_ROOT: Result<(), StateTransportError> = Err(StateTransportError::InvalidTerm(
    StateTermReason::KeptRestOutsideListCellRoot,
));

/// A list cell entry's root brackets end in the list's unnamed rest, on either side of a rule
/// with a result: a cons level's tail, a snoc level's init, at any depth of the root's spine,
/// the root itself (`[..]`, a spine of no level), below `Some(..)` too.
#[test]
fn a_kept_rest_ends_a_list_cell_entrys_root_spine() {
    use crate::ListNotation::{Cons, Snoc};
    for (side, validation) in [
        (RuleSide::Left, ValidationSide::Left),
        (RuleSide::Right, ValidationSide::Right),
    ] {
        let literal = |ordinal| {
            list_literal(
                match side {
                    RuleSide::Left => ProvenanceRole::RuleLeftLiteral,
                    RuleSide::Right => ProvenanceRole::RuleRightLiteral,
                },
                ordinal,
            )
        };
        let terms = [
            // `[..]`, `[x, ..]`, `[.., x]` and `[x, .., y]`.
            kept_rest(validation, 0),
            list_level(validation, Cons, literal(0), kept_rest(validation, 0), 0),
            list_level(validation, Snoc, literal(0), kept_rest(validation, 0), 0),
            list_level(
                validation,
                Cons,
                literal(0),
                list_level(validation, Snoc, literal(1), kept_rest(validation, 0), 1),
                0,
            ),
        ];
        for term in terms {
            let state = ProtocolRuleStateTerm::Term(term);
            assert_eq!(list_entry(&state, side, true, true), Ok(()));
            let present = ProtocolRuleStateTerm::Present {
                value: Box::new(state),
            };
            assert_eq!(list_entry(&present, side, true, true), Ok(()));
        }
    }
}

/// The whole entry is the list's rest only where it is a list cell entry's root (`Cell([..])`):
/// elsewhere, as an instance child's whole term, it is no list cell's rest.
#[test]
fn a_kept_rest_is_a_whole_entry_only_at_a_list_cells_root() {
    let state = ProtocolRuleStateTerm::Term(kept_rest(ValidationSide::Right, 0));
    assert_eq!(list_entry(&state, RuleSide::Right, true, true), Ok(()));
    assert_eq!(
        list_entry(&state, RuleSide::Right, false, true),
        OUTSIDE_LIST_ROOT
    );
}

/// An element of the root's brackets, and a list nested in one, are no rest of the cell's list.
#[test]
fn a_kept_rest_is_not_an_element_or_a_nested_lists_rest() {
    use crate::ListNotation::Cons;
    let left = ValidationSide::Left;
    let literal = |ordinal| list_literal(ProvenanceRole::RuleLeftLiteral, ordinal);
    for term in [
        // `[.., ..rest]`'s element.
        list_level(left, Cons, kept_rest(left, 0), literal(0), 0),
        // `[[x, ..], ..rest]`.
        list_level(
            left,
            Cons,
            list_level(left, Cons, literal(0), kept_rest(left, 0), 1),
            literal(1),
            0,
        ),
    ] {
        assert_eq!(
            list_entry(
                &ProtocolRuleStateTerm::Term(term),
                RuleSide::Left,
                true,
                true
            ),
            OUTSIDE_LIST_ROOT
        );
    }
}

/// A term below an application that is no level of list notation is no rest of the list.
#[test]
fn a_kept_rest_is_not_an_applications_argument() {
    let head = key(ProvenanceRole::RuleLeftApplicationHead);
    let term = Term::Application {
        instance: Vec::new(),
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: DescriptorApplicationReference {
            key: head.clone(),
            application: DescriptorApplicationRef::Declared(item("Wrap", ItemKind::Constructor)),
        },
        path_key: head,
        arguments: crate::Arguments::Positional(vec![Box::new(kept_rest(ValidationSide::Left, 0))]),
        update: None,
        open: false,
    };
    assert_eq!(
        list_entry(
            &ProtocolRuleStateTerm::Term(term),
            RuleSide::Left,
            true,
            true
        ),
        OUTSIDE_LIST_ROOT
    );
}

/// A sentence with no result (a single-body rule, a context) keeps no rest, so its subject's
/// brackets hold none.
#[test]
fn a_kept_rest_needs_a_result_to_keep_it() {
    let left = ValidationSide::Left;
    let term = list_level(
        left,
        crate::ListNotation::Cons,
        list_literal(ProvenanceRole::RuleLeftLiteral, 0),
        kept_rest(left, 0),
        0,
    );
    assert_eq!(
        list_entry(
            &ProtocolRuleStateTerm::Term(term),
            RuleSide::Left,
            true,
            false
        ),
        OUTSIDE_LIST_ROOT
    );
}

/// A collection instance's child is no entry's root: its list's rest is not the cell's.
#[test]
fn a_kept_rest_is_not_an_instance_childs() {
    let left = ValidationSide::Left;
    let term = list_level(
        left,
        crate::ListNotation::Cons,
        list_literal(ProvenanceRole::RuleLeftLiteral, 0),
        kept_rest(left, 0),
        0,
    );
    let child = ProtocolRuleStateTerm::Term(term);
    // The child's own validation, as an instance's field validates it.
    assert_eq!(
        list_entry(&child, RuleSide::Left, false, true),
        OUTSIDE_LIST_ROOT
    );
}

/// A K sequence's item and a condition hold no list cell's rest.
#[test]
fn a_kept_rest_is_not_in_a_k_sequence_or_a_condition() {
    let rest = kept_rest(ValidationSide::Left, 0);
    let sequence = ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
        payload_key: key(ProvenanceRole::RuleLeftKSequencePayload),
        dot_k_key: None,
        notation: crate::DescriptorKSequenceNotation::Comma,
        items: vec![ProtocolRuleKSequenceItem {
            key: key(ProvenanceRole::RuleLeftKSequenceItem),
            value: rest,
        }],
        tail: ProtocolRuleFrame::Exact,
    });
    assert_eq!(
        list_entry(&sequence, RuleSide::Left, true, true),
        OUTSIDE_LIST_ROOT
    );
    assert_eq!(
        validate_rule_term(
            &kept_rest(ValidationSide::Right, 0),
            ValidationSide::Requires,
            &[],
            &mut Vec::new(),
            &mut RuleWalk {
                kept_rests: true,
                in_list_root: true,
                ..RuleWalk::default()
            },
            &mut WireKeys::default(),
        ),
        OUTSIDE_LIST_ROOT
    );
}

/// A map pattern `map![true -> true, ..]` keyed on `side`, its rest `..` a wildcard.
fn map_pattern(side: ValidationSide, rest: Option<Term<DescriptorStage>>) -> Term<DescriptorStage> {
    let literal = match side {
        ValidationSide::Left => ProvenanceRole::RuleLeftLiteral,
        _ => ProvenanceRole::RuleRightLiteral,
    };
    Term::MapEntries {
        key: key(ProvenanceRole::PatternMap),
        entries: vec![crate::MapTermEntry {
            key: Box::new(list_literal(literal, 0)),
            value: Box::new(list_literal(literal, 1)),
        }],
        rest: rest.map(Box::new),
    }
}

fn validate_on(
    term: &Term<DescriptorStage>,
    side: ValidationSide,
) -> Result<(), StateTransportError> {
    validate_rule_term(
        term,
        side,
        &[],
        &mut Vec::new(),
        &mut RuleWalk::default(),
        &mut WireKeys::default(),
    )
}

/// A map pattern is matched where a subject is, with or without its rest; a term a sentence
/// builds holds none, and its rest is a variable or `_`.
#[test]
fn a_map_pattern_stands_only_in_a_pattern() {
    let wildcard = Term::Wildcard {
        key: key(ProvenanceRole::RuleLeftWildcard),
    };
    assert_eq!(
        validate_on(
            &map_pattern(ValidationSide::Left, Some(wildcard.clone())),
            ValidationSide::Left
        ),
        Ok(())
    );
    assert_eq!(
        validate_on(
            &map_pattern(ValidationSide::Left, None),
            ValidationSide::Left
        ),
        Ok(())
    );
    assert_eq!(
        validate_on(
            &map_pattern(ValidationSide::Right, None),
            ValidationSide::Right
        ),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::MapPatternOutsidePattern
        ))
    );
    assert_eq!(
        validate_on(
            &map_pattern(
                ValidationSide::Left,
                Some(list_literal(ProvenanceRole::RuleLeftLiteral, 2))
            ),
            ValidationSide::Left
        ),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::MalformedMapPattern
        ))
    );
    let empty = Term::MapEntries {
        key: key(ProvenanceRole::PatternMap),
        entries: Vec::new(),
        rest: Some(Box::new(wildcard)),
    };
    assert_eq!(
        validate_on(&empty, ValidationSide::Left),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::MalformedMapPattern
        ))
    );
}
