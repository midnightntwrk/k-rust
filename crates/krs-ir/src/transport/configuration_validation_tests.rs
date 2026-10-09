use super::*;
use crate::transport::detail::{
    StateCellContentReason, StateTermReason, TransportField, TransportItemKind,
};
use crate::transport::grammar::TermArgument;

use crate::transport::grammar::{
    DescriptorApplicationRef, DescriptorApplicationReference, HostApplicationReference,
    HostApplicationTarget,
};

struct Owner;
struct Field;
struct Sort;
struct Nested;

fn type_id<T: 'static>() -> TypeId {
    TypeId::of::<T>()
}

fn type_key<T: 'static>() -> HostTypeKey {
    HostTypeKey(type_id::<T>)
}

fn item(kind: ItemKind) -> StableItemId {
    crate::testing::item("transport", "Owner", kind)
}

fn key(role: ProvenanceRole) -> ProvenanceKey {
    ProvenanceKey::new(role, 0)
}

fn descriptor_sort(role: ProvenanceRole) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(role),
        sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
    }
}

fn host_sort(role: ProvenanceRole) -> HostSortReference {
    HostSortReference {
        key: key(role),
        target: HostTypeReference {
            key: type_key::<Sort>(),
            authored_path: String::new(),
        },
    }
}

fn descriptor_reference(role: ProvenanceRole) -> DescriptorCellReference {
    DescriptorCellReference {
        key: key(role),
        cell: DescriptorCellIdentity {
            owner: item(ItemKind::Configuration),
            field: "value".into(),
        },
    }
}

fn host_reference(role: ProvenanceRole) -> HostCellReference {
    HostCellReference {
        key: key(role),
        cell: HostCellIdentity {
            owner: type_key::<Owner>(),
            field: type_key::<Field>(),
        },
    }
}

fn declaration<S: Stage>(reference: S::Cell, sort: S::Sort) -> StageCellDeclaration<S> {
    ProtocolCellDeclaration {
        key: key(ProvenanceRole::ConfigurationDeclaration),
        fields: vec![ProtocolCellField {
            reference,
            rust_field: "value".into(),
            emitted_name: None,
            color: None,
            multiplicity: None,
            cell_type: None,
            stream: None,
            exit: None,
            content: ProtocolCellContent::Leaf {
                wrapper_key: key(ProvenanceRole::ConfigurationCellWrapper),
                wrapper: CellWrapper::Cell,
                sort,
                arguments: Vec::new(),
            },
        }],
    }
}

fn initializer_cell<S: Stage>(field: S::Cell) -> StageInitializerCell<S> {
    ProtocolInitializerCell {
        key: key(ProvenanceRole::InitializerCell),
        field,
        content: ProtocolInitializerCellContent::Leaf {
            constructor_key: key(ProvenanceRole::InitializerCellConstructor),
            wrapper: CellWrapper::Cell,
            value: ProtocolInitializerStateTerm::Term(ProtocolInitializerTerm {
                key: key(ProvenanceRole::InitializerTerm),
                term: Term::Literal {
                    key: key(ProvenanceRole::InitializerTerm),
                    literal: DescriptorLiteral::Int("1".into()),
                },
            }),
        },
    }
}

fn fixed_configuration<S: Stage>(
    owner: S::InitializerOwner,
    declaration: StageCellDeclaration<S>,
    cell: StageInitializerCell<S>,
) -> FixedConfiguration<S> {
    FixedConfiguration {
        root: DescriptorConfigurationRoot::GeneratedTop,
        declaration,
        initializer: ProtocolConfigurationInitializer {
            key: key(ProvenanceRole::InitializerDeclaration),
            owner_key: key(ProvenanceRole::InitializerResultType),
            owner,
            variables: Vec::new(),
            body_key: key(ProvenanceRole::InitializerBody),
            cells: vec![cell],
        },
    }
}

#[test]
fn fixed_configuration_owner_hooks_preserve_first_errors_and_host_aliases() {
    let mut descriptor = fixed_configuration::<DescriptorStage>(
        item(ItemKind::Configuration),
        declaration::<DescriptorStage>(
            descriptor_reference(ProvenanceRole::ConfigurationField),
            descriptor_sort(ProvenanceRole::ConfigurationCellContent),
        ),
        initializer_cell::<DescriptorStage>(descriptor_reference(ProvenanceRole::InitializerField)),
    );
    assert_eq!(descriptor.validate(&item(ItemKind::Configuration)), Ok(()));
    descriptor.initializer.owner = item(ItemKind::Cell);
    assert_eq!(
        descriptor.validate(&item(ItemKind::Configuration)),
        Err(StateTransportError::InitializerDeclarationMismatch)
    );
    descriptor.root = DescriptorConfigurationRoot::Named {
        key: key(ProvenanceRole::InitializerDeclaration),
        name: "root".into(),
    };
    assert_eq!(
        descriptor.validate(&item(ItemKind::Cell)),
        Err(StateTransportError::ItemKind {
            field: TransportField::ConfigurationDescriptor,
            expected: TransportItemKind::Configuration,
            actual: ItemKind::Cell,
        })
    );

    let mut host = fixed_configuration::<HostStage>(
        type_key::<Owner>(),
        declaration::<HostStage>(
            host_reference(ProvenanceRole::ConfigurationField),
            host_sort(ProvenanceRole::ConfigurationCellContent),
        ),
        initializer_cell::<HostStage>(host_reference(ProvenanceRole::InitializerField)),
    );
    let alias = HostTypeKey(TypeId::of::<Owner>);
    assert_eq!(host.validate(alias), Ok(()));
    host.initializer.owner = type_key::<Nested>();
    assert_eq!(
        host.validate(type_key::<Owner>()),
        Err(StateTransportError::InitializerDeclarationMismatch)
    );
    host.root = descriptor.root;
    assert_eq!(
        host.validate(type_key::<Nested>()),
        Err(StateTransportError::UnexpectedProvenance {
            expected: key(ProvenanceRole::ConfigurationRoot),
            actual: key(ProvenanceRole::InitializerDeclaration),
        })
    );
}

#[test]
fn stable_cell_identity_checks_precede_ownership_and_field_spelling() {
    let mut descriptor = declaration::<DescriptorStage>(
        descriptor_reference(ProvenanceRole::ConfigurationField),
        descriptor_sort(ProvenanceRole::ConfigurationCellContent),
    );
    descriptor.fields[0].reference.cell.owner = item(ItemKind::Sort);
    descriptor.fields[0].reference.cell.field = "/".into();
    assert_eq!(
        descriptor.validate(&item(ItemKind::Configuration)),
        Err(StateTransportError::ItemKind {
            field: TransportField::CellIdentityOwner,
            expected: TransportItemKind::ConfigurationOrCell,
            actual: ItemKind::Sort,
        })
    );
    descriptor.fields[0].reference.cell.owner = item(ItemKind::Configuration);
    assert_eq!(
        descriptor.validate(&item(ItemKind::Configuration)),
        Err(StateTransportError::InvalidText(
            TransportField::RustFieldIdentity
        ))
    );
    descriptor.fields[0].reference.cell.field = "other".into();
    assert_eq!(
        descriptor.validate(&item(ItemKind::Configuration)),
        Err(StateTransportError::CellFieldMismatch)
    );

    let mut host = declaration::<HostStage>(
        host_reference(ProvenanceRole::ConfigurationField),
        host_sort(ProvenanceRole::ConfigurationCellContent),
    );
    host.fields[0].rust_field = "other".into();
    assert_eq!(host.validate_host(type_key::<Owner>()), Ok(()));
    assert_eq!(
        host.validate_host(type_key::<Nested>()),
        Err(StateTransportError::CellOwnerMismatch)
    );
}

#[test]
fn declaration_owner_kinds_precede_provenance_only_for_descriptors() {
    let descriptor = ProtocolCellDeclaration::<DescriptorCellField> {
        key: key(ProvenanceRole::InitializerDeclaration),
        fields: Vec::new(),
    };
    assert_eq!(
        descriptor.validate(&item(ItemKind::Sort)),
        Err(StateTransportError::ItemKind {
            field: TransportField::CellDeclaration,
            expected: TransportItemKind::ConfigurationOrCell,
            actual: ItemKind::Sort,
        })
    );
    let host = ProtocolCellDeclaration::<HostCellField> {
        key: descriptor.key.clone(),
        fields: Vec::new(),
    };
    assert_eq!(
        host.validate_host(type_key::<Owner>()),
        Err(StateTransportError::UnexpectedProvenance {
            expected: key(ProvenanceRole::ConfigurationDeclaration),
            actual: descriptor.key,
        })
    );
}

#[test]
fn leaf_sorts_preserve_descriptor_only_kind_and_k_sequence_checks() {
    let mut descriptor = descriptor_sort(ProvenanceRole::ConfigurationCellContent);
    descriptor.sort = DescriptorSortRef::Declared(item(ItemKind::Cell));
    assert_eq!(
        DescriptorStage::validate_leaf_sort(CellWrapper::KCell, &descriptor),
        Err(StateTransportError::ItemKind {
            field: TransportField::CellContentSort,
            expected: TransportItemKind::SortOrBuiltin,
            actual: ItemKind::Cell,
        })
    );
    descriptor.sort = DescriptorSortRef::Builtin(BuiltinSort::Int);
    assert_eq!(
        DescriptorStage::validate_leaf_sort(CellWrapper::KCell, &descriptor),
        Err(StateTransportError::InvalidCellContent(
            StateCellContentReason::KCellSortMismatch
        ))
    );
    descriptor.sort = DescriptorSortRef::Builtin(BuiltinSort::KSequence);
    assert_eq!(
        DescriptorStage::validate_leaf_sort(CellWrapper::KCell, &descriptor),
        Ok(())
    );
    assert_eq!(
        HostStage::validate_leaf_sort(
            CellWrapper::KCell,
            &host_sort(ProvenanceRole::ConfigurationCellContent)
        ),
        Ok(())
    );
    descriptor.sort = DescriptorSortRef::Declared(item(ItemKind::Cell));
    descriptor.key = key(ProvenanceRole::InitializerTerm);
    let descriptor = declaration::<DescriptorStage>(
        descriptor_reference(ProvenanceRole::ConfigurationField),
        descriptor,
    );
    let expected = Err(StateTransportError::UnexpectedProvenance {
        expected: key(ProvenanceRole::ConfigurationCellContent),
        actual: key(ProvenanceRole::InitializerTerm),
    });
    assert_eq!(
        descriptor.validate(&item(ItemKind::Configuration)),
        expected
    );
    let host = declaration::<HostStage>(
        host_reference(ProvenanceRole::ConfigurationField),
        host_sort(ProvenanceRole::InitializerTerm),
    );
    assert_eq!(host.validate_host(type_key::<Owner>()), expected);
}

#[test]
fn cell_sort_arguments_keep_stage_specific_target_checks() {
    let mut descriptor = descriptor_sort(ProvenanceRole::ConfigurationCellContentArgument);
    descriptor.sort = DescriptorSortRef::Declared(item(ItemKind::Cell));
    assert_eq!(
        DescriptorStage::validate_sort_argument(&descriptor),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidCellSortArgument
        ))
    );
    descriptor.sort = DescriptorSortRef::Builtin(BuiltinSort::Int);
    assert_eq!(DescriptorStage::validate_sort_argument(&descriptor), Ok(()));
    let mut host = host_sort(ProvenanceRole::ConfigurationCellContentArgument);
    assert_eq!(
        HostStage::validate_sort_argument(&host),
        Err(StateTransportError::InvalidText(
            TransportField::CellSortArgumentDiagnosticPath
        ))
    );
    host.target.authored_path = "Alias".into();
    assert_eq!(HostStage::validate_sort_argument(&host), Ok(()));
}

#[test]
fn nested_targets_keep_distinct_declaration_and_initializer_checks() {
    let mut descriptor = DescriptorCellDeclarationReference {
        key: key(ProvenanceRole::ConfigurationCellContent),
        declaration: item(ItemKind::Configuration),
    };
    let error = Err(StateTransportError::ItemKind {
        field: TransportField::NestedCellDeclaration,
        expected: TransportItemKind::Cell,
        actual: ItemKind::Configuration,
    });
    assert_eq!(
        DescriptorStage::validate_nested_declaration(&descriptor),
        error
    );
    assert_eq!(
        DescriptorStage::validate_nested_initializer(&descriptor),
        error
    );
    descriptor.declaration = item(ItemKind::Cell);
    assert_eq!(
        DescriptorStage::validate_nested_declaration(&descriptor),
        Ok(())
    );
    assert_eq!(
        DescriptorStage::validate_nested_initializer(&descriptor),
        Ok(())
    );
    let mut host = HostCellDeclarationReference {
        key: descriptor.key,
        declaration: HostTypeReference {
            key: type_key::<Nested>(),
            authored_path: String::new(),
        },
    };
    assert_eq!(
        HostStage::validate_nested_declaration(&host),
        Err(StateTransportError::InvalidText(
            TransportField::NestedCellDiagnosticPath
        ))
    );
    assert_eq!(HostStage::validate_nested_initializer(&host), Ok(()));
    host.declaration.authored_path = "Alias".into();
    assert_eq!(HostStage::validate_nested_declaration(&host), Ok(()));
}

#[test]
fn initializer_field_joins_check_stable_spelling_only_for_descriptors() {
    let mut descriptor = declaration::<DescriptorStage>(
        descriptor_reference(ProvenanceRole::ConfigurationField),
        descriptor_sort(ProvenanceRole::ConfigurationCellContent),
    );
    descriptor.fields[0].rust_field = "other".into();
    let cells = vec![initializer_cell::<DescriptorStage>(descriptor_reference(
        ProvenanceRole::InitializerField,
    ))];
    assert_eq!(
        validate_initializer_cells::<DescriptorStage>(
            &cells,
            &descriptor.fields,
            &item(ItemKind::Configuration),
            &BTreeSet::new(),
            &mut InitializerCounters::default(),
            &mut BTreeSet::new(),
        ),
        Err(StateTransportError::InitializerDeclarationMismatch)
    );
    let mut host = declaration::<HostStage>(
        host_reference(ProvenanceRole::ConfigurationField),
        host_sort(ProvenanceRole::ConfigurationCellContent),
    );
    host.fields[0].rust_field = "other".into();
    let cells = vec![initializer_cell::<HostStage>(host_reference(
        ProvenanceRole::InitializerField,
    ))];
    assert_eq!(
        validate_initializer_cells::<HostStage>(
            &cells,
            &host.fields,
            &type_key::<Owner>(),
            &BTreeSet::new(),
            &mut InitializerCounters::default(),
            &mut BTreeSet::new(),
        ),
        Ok(())
    );
}

fn variable<S>(sort: S) -> ProtocolConfigurationVariable<S> {
    ProtocolConfigurationVariable {
        binding_key: key(ProvenanceRole::ConfigurationVariable),
        binding: "input".into(),
        external_name_key: key(ProvenanceRole::ConfigurationVariableName),
        external_name: "$INPUT".into(),
        sort,
        main_key: None,
    }
}

#[test]
fn initializer_variable_sorts_are_checked_only_for_descriptors() {
    let mut sort = descriptor_sort(ProvenanceRole::ConfigurationVariableType);
    sort.sort = DescriptorSortRef::Declared(item(ItemKind::Cell));
    assert_eq!(
        validate_variables::<DescriptorStage>(&[variable(sort)], &mut BTreeSet::new()),
        Err(StateTransportError::InvalidCellContent(
            StateCellContentReason::InvalidVariableSort
        ))
    );
    assert_eq!(
        validate_variables::<HostStage>(
            &[variable(host_sort(
                ProvenanceRole::ConfigurationVariableType
            ))],
            &mut BTreeSet::new()
        ),
        Ok(BTreeSet::from(["input".into()]))
    );
}

fn initializer_term<S: ConfigurationValidationStage>(
    term: Term<S>,
) -> Result<(), StateTransportError> {
    validate_initializer_term::<S>(
        &ProtocolInitializerTerm {
            key: key(ProvenanceRole::InitializerTerm),
            term,
        },
        &BTreeSet::new(),
        &mut InitializerCounters::default(),
        &mut BTreeSet::new(),
        None,
    )
}

#[test]
fn initializer_application_targets_are_checked_only_for_descriptors() {
    let path_key = key(ProvenanceRole::InitializerTermPath);
    assert_eq!(
        initializer_term::<DescriptorStage>(Term::Application {
            instance: Vec::new(),
            head_class: DescriptorApplicationHeadClass::BareReference,
            reference: DescriptorApplicationReference {
                key: path_key.clone(),
                application: DescriptorApplicationRef::Declared(item(ItemKind::Sort)),
            },
            path_key: path_key.clone(),
            arguments: crate::Arguments::default(),
        }),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidApplicationTarget
        ))
    );
    assert_eq!(
        initializer_term::<HostStage>(Term::Application {
            instance: Vec::new(),
            head_class: DescriptorApplicationHeadClass::BareReference,
            reference: HostApplicationReference {
                key: path_key.clone(),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: type_key::<Sort>(),
                    authored_path: String::new(),
                }),
            },
            path_key,
            arguments: crate::Arguments::default(),
        }),
        Ok(())
    );
}

fn assert_initializer_context<S: ConfigurationValidationStage>() {
    assert_eq!(
        initializer_term::<S>(Term::Wildcard {
            key: key(ProvenanceRole::InitializerTermPath)
        }),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::WildcardsAreNotAllowedInInitializers
        ))
    );
    assert_eq!(
        initializer_term::<S>(Term::OrBool {
            key: key(ProvenanceRole::InitializerTerm),
            arguments: crate::AtLeastTwo::new(
                Term::Wildcard {
                    key: key(ProvenanceRole::InitializerTermPath)
                },
                Term::Wildcard {
                    key: key(ProvenanceRole::InitializerTermPath)
                },
                Vec::new()
            ),
        }),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerClaimTerm
        ))
    );
    assert_eq!(
        initializer_term::<S>(Term::Literal {
            key: key(ProvenanceRole::InitializerTermPath),
            literal: DescriptorLiteral::Int("-0".into()),
        }),
        Err(StateTransportError::UnexpectedProvenance {
            expected: key(ProvenanceRole::InitializerTerm),
            actual: key(ProvenanceRole::InitializerTermPath),
        })
    );
    assert_eq!(
        initializer_term::<S>(Term::Literal {
            key: key(ProvenanceRole::InitializerTerm),
            literal: DescriptorLiteral::Int("-0".into()),
        }),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::NonCanonicalIntegerLiteral
        ))
    );
}

#[test]
fn initializer_context_preserves_restrictions_and_first_errors_on_both_stages() {
    assert_initializer_context::<DescriptorStage>();
    assert_initializer_context::<HostStage>();
}

fn assert_argument_context<S: ConfigurationValidationStage>(reference: &S::Application) {
    let named = || TermArgument::Named {
        key: key(ProvenanceRole::InitializerTermPath),
        field: ProductionFieldId::new("value").unwrap(),
        value: Box::new(Term::Wildcard {
            key: key(ProvenanceRole::InitializerTermPath),
        }),
    };
    let application = |arguments| Term::Application {
        instance: Vec::new(),
        head_class: DescriptorApplicationHeadClass::Applied,
        path_key: key(ProvenanceRole::InitializerTermPath),
        reference: reference.clone(),
        arguments: crate::Arguments::try_from(arguments).unwrap(),
    };
    assert_eq!(
        initializer_term::<S>(application(vec![named()])),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerRecordFieldProvenance
        ))
    );
    assert!(matches!(
        crate::Arguments::<S>::try_from(vec![
            TermArgument::Positional {
                value: Box::new(Term::Wildcard {
                    key: key(ProvenanceRole::InitializerTermPath)
                })
            },
            named(),
        ]),
        Err(crate::ArgumentsError::MixedForms)
    ));
}

#[test]
fn initializer_arguments_preserve_child_before_next_argument_order_on_both_stages() {
    assert_argument_context::<DescriptorStage>(&DescriptorApplicationReference {
        key: key(ProvenanceRole::InitializerTermPath),
        application: DescriptorApplicationRef::Declared(item(ItemKind::Constructor)),
    });
    assert_argument_context::<HostStage>(&HostApplicationReference {
        key: key(ProvenanceRole::InitializerTermPath),
        target: HostApplicationTarget::Nominal(HostTypeReference {
            key: type_key::<Sort>(),
            authored_path: String::new(),
        }),
    });
}

#[test]
fn nested_reference_joins_compare_identities_and_ignore_host_path_spelling() {
    let descriptor = DescriptorCellDeclarationReference {
        key: key(ProvenanceRole::ConfigurationCellContent),
        declaration: item(ItemKind::Cell),
    };
    let mut other = descriptor.clone();
    other.declaration = item(ItemKind::Configuration);
    assert!(DescriptorStage::nested_declarations_match(
        &descriptor,
        &descriptor
    ));
    assert!(!DescriptorStage::nested_declarations_match(
        &descriptor,
        &other
    ));
    assert_eq!(
        DescriptorStage::nested_owner(&descriptor),
        descriptor.declaration
    );
    let host = HostCellDeclarationReference {
        key: descriptor.key,
        declaration: HostTypeReference {
            key: type_key::<Nested>(),
            authored_path: "Nested".into(),
        },
    };
    let mut alias = host.clone();
    alias.declaration.key = HostTypeKey(TypeId::of::<Nested>);
    alias.declaration.authored_path = "Alias".into();
    assert!(HostStage::nested_declarations_match(&host, &alias));
    alias.declaration.key = type_key::<Owner>();
    assert!(!HostStage::nested_declarations_match(&host, &alias));
    assert_eq!(
        HostStage::nested_owner(&host).resolve(),
        TypeId::of::<Nested>()
    );
}

fn assert_duplicate_nested_children<S: ConfigurationValidationStage>(
    reference: S::Cell,
    owner: &S::InitializerOwner,
) {
    let cells = [
        initializer_cell::<S>(reference.clone()),
        initializer_cell::<S>(reference),
    ];
    assert_eq!(
        validate_nested_children::<S>(
            &cells,
            owner,
            &BTreeSet::new(),
            &mut InitializerCounters::default(),
            &mut BTreeSet::new(),
        ),
        Err(StateTransportError::InitializerDeclarationMismatch)
    );
}

#[test]
fn cell_and_sibling_identities_preserve_owner_and_field_comparisons_on_both_stages() {
    let descriptor = descriptor_reference(ProvenanceRole::InitializerField);
    let mut other_descriptor = descriptor.clone();
    other_descriptor.cell.owner = item(ItemKind::Cell);
    assert_ne!(
        DescriptorStage::cell_identity(&descriptor),
        DescriptorStage::cell_identity(&other_descriptor)
    );
    assert_eq!(
        DescriptorStage::field_identity(&descriptor),
        DescriptorStage::field_identity(&other_descriptor)
    );
    assert_duplicate_nested_children::<DescriptorStage>(descriptor, &item(ItemKind::Configuration));
    let host = host_reference(ProvenanceRole::InitializerField);
    let mut other_host = host.clone();
    other_host.cell.owner = type_key::<Nested>();
    assert_ne!(
        HostStage::cell_identity(&host),
        HostStage::cell_identity(&other_host)
    );
    assert_eq!(
        HostStage::field_identity(&host),
        HostStage::field_identity(&other_host)
    );
    other_host.cell.owner = HostTypeKey(TypeId::of::<Owner>);
    other_host.cell.field = HostTypeKey(TypeId::of::<Field>);
    assert_eq!(
        HostStage::cell_identity(&host),
        HostStage::cell_identity(&other_host)
    );
    assert_duplicate_nested_children::<HostStage>(host, &type_key::<Owner>());
}
