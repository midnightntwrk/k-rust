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
        &mut RuleCounters::default(),
        &mut BTreeSet::new(),
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
            0,
            &mut BTreeSet::new()
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
            0,
            &mut BTreeSet::new()
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
            0,
            &mut BTreeSet::new()
        ),
        Err(StateTransportError::UnexpectedProvenance {
            expected: key(ProvenanceRole::ClaimBinderSort),
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
        validate_rule_binding_catalog::<DescriptorStage>(&descriptor, &mut BTreeSet::new()),
        Err(StateTransportError::ItemKind {
            field: TransportField::RuleBindingSort,
            expected: TransportItemKind::Sort,
            actual: ItemKind::Constructor,
        })
    );
    assert!(validate_rule_binding_catalog::<HostStage>(&host, &mut BTreeSet::new()).is_ok());
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
        spelling: "_value".into(),
    };
    let mut host: Term<HostStage> = Term::Anonymous {
        key: key(ProvenanceRole::ClaimAnonymous),
        sort: host_sort(ProvenanceRole::ClaimAnonymousSort),
        spelling: "_value".into(),
    };
    assert_eq!(
        check_term(&descriptor),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidAnonymousSort
        ))
    );
    assert!(check_term(&host).is_ok());
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
            expected: key(ProvenanceRole::ClaimAnonymous),
            actual: key(ProvenanceRole::RuleLeftLiteral),
        })
    );
}

#[test]
fn fragments_preserve_stage_specific_declaration_and_empty_errors() {
    let mut descriptor: Term<DescriptorStage> = Term::Cell {
        key: key(ProvenanceRole::RuleLeftApplicationHead),
        declaration: item("Target", ItemKind::Sort),
        fields: Vec::new(),
    };
    let mut host: Term<HostStage> = Term::Cell {
        key: key(ProvenanceRole::RuleLeftApplicationHead),
        declaration: host_type::<()>(),
        fields: Vec::new(),
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
            &mut RuleCounters::default(),
            &mut BTreeSet::new()
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
            &mut RuleCounters::default(),
            &mut BTreeSet::new()
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
            &mut RuleCounters::default(),
            &mut BTreeSet::new()
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
            &mut RuleCounters::default(),
            &mut BTreeSet::new()
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
            &mut RuleCounters::default(),
            &mut BTreeSet::new(),
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
    }
}

#[test]
fn context_aliases_preserve_stage_specific_early_checks() {
    let descriptor = alias::<DescriptorStage>(DescriptorConfigurationReference {
        key: key(ProvenanceRole::RuleType),
        configuration: item("Config", ItemKind::Configuration),
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
        },
        DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleResultType),
            configuration: item("Config", ItemKind::Configuration),
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
    let mut descriptor_keys = BTreeSet::new();
    let mut host_keys = BTreeSet::new();
    validate_configuration_rule(&descriptor, ItemKind::Rule, &mut descriptor_keys).unwrap();
    validate_configuration_rule(&host, ItemKind::Rule, &mut host_keys).unwrap();
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
        },
        DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleResultType),
            configuration: item("Other", ItemKind::Configuration),
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
