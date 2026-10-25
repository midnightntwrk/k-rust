//! The configuration fixture bundle: a `Machine` with a computation cell and a map cell, the
//! framework `KItem`, a `Value` sort, and one rule that moves a map value into the computation.

use krs_ir::testing::{DescriptorBundleInputs, DescriptorInputs};

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::testing;
use krs_ir::{
    BuiltinSort, CellWrapper, DescriptorCellField, DescriptorCellIdentity, DescriptorCellReference,
    DescriptorConfigurationDeclaration, DescriptorConfigurationInitializer,
    DescriptorConfigurationReference, DescriptorConfigurationRoot, DescriptorConfigurationRule,
    DescriptorConfigurationVariable, DescriptorFixedConfiguration, DescriptorInitializerCell,
    DescriptorNodeOrigin, DescriptorPayload, DescriptorProvenance, DescriptorRuleBinding,
    DescriptorRuleCells, DescriptorSortRef, DescriptorSortReference, DescriptorTerm, ItemKind,
    PackageId, ProtocolCellContent, ProtocolConfigurationVariable, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolInitializerTerm, ProtocolKSequence,
    ProtocolKSequenceItem, ProtocolRuleBinding, ProtocolRuleBindingKind, ProtocolRuleCell,
    ProtocolRuleFrame, ProtocolRuleKSequence, ProtocolRuleKSequenceItem, ProtocolRuleMap,
    ProtocolRuleMapBody, ProtocolRuleMapItem, ProtocolRuleStateTerm, ProvenanceKey, ProvenanceRole,
    RuleSide, SortDescriptor, StableItemId,
};

pub fn package() -> PackageId {
    testing::package("KRS-STATE", "state")
}

pub fn id(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "calc", name, kind)
}

pub fn framework_kitem() -> StableItemId {
    testing::item_in(
        testing::package_with("KRS-FRAMEWORK", "krs", "0.1.0", "framework"),
        "framework",
        "KItem",
        ItemKind::Sort,
    )
}

pub fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal)
}

pub fn provenance(
    primary: ProvenanceKey,
    keys: impl IntoIterator<Item = ProvenanceKey>,
) -> DescriptorProvenance {
    let mut keys = std::iter::once(primary.clone())
        .chain(keys)
        .collect::<Vec<_>>();
    keys.sort();
    keys.dedup();
    DescriptorProvenance::new(
        primary,
        keys.into_iter()
            .enumerate()
            .map(|(index, key)| {
                let start = u32::try_from(index).unwrap();
                DescriptorNodeOrigin::new(
                    key,
                    testing::authored_in(
                        package(),
                        "src/calc.rs",
                        testing::digest_with("7".repeat(64)),
                        start,
                        start + 1,
                    ),
                )
            })
            .collect(),
    )
    .unwrap()
}

pub fn sort_ref(
    role: ProvenanceRole,
    ordinal: u32,
    sort: DescriptorSortRef,
) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(role, ordinal),
        sort,
    }
}

pub fn cell_field(
    owner: &StableItemId,
    ordinal: u32,
    name: &str,
    wrapper: CellWrapper,
    sort: BuiltinSort,
) -> DescriptorCellField {
    DescriptorCellField {
        reference: DescriptorCellReference {
            key: key(ProvenanceRole::ConfigurationField, ordinal),
            cell: DescriptorCellIdentity {
                owner: owner.clone(),
                field: name.into(),
            },
        },
        rust_field: name.into(),
        emitted_name: None,
        color: None,
        multiplicity: None,
        cell_type: None,
        stream: None,
        exit: None,
        initial: None,
        content: ProtocolCellContent::Leaf {
            wrapper_key: key(ProvenanceRole::ConfigurationCellWrapper, ordinal),
            wrapper,
            sort: sort_ref(
                ProvenanceRole::ConfigurationCellContent,
                ordinal,
                DescriptorSortRef::Builtin(sort),
            ),
            arguments: Vec::new(),
        },
    }
}

pub fn initializer_variable(
    ordinal: u32,
    binding: &str,
    external: &str,
    sort: BuiltinSort,
    main: bool,
) -> DescriptorConfigurationVariable {
    ProtocolConfigurationVariable {
        binding_key: key(ProvenanceRole::ConfigurationVariable, ordinal),
        binding: binding.into(),
        external_name_key: key(ProvenanceRole::ConfigurationVariableName, ordinal),
        external_name: external.into(),
        sort: sort_ref(
            ProvenanceRole::ConfigurationVariableType,
            ordinal,
            DescriptorSortRef::Builtin(sort),
        ),
        arguments: Vec::new(),
        main_key: main.then(|| key(ProvenanceRole::ConfigurationVariableMain, ordinal)),
    }
}

pub fn variable(role: ProvenanceRole, ordinal: u32, name: &str) -> DescriptorTerm {
    let key = key(role, ordinal);
    DescriptorTerm::Variable {
        key: key.clone(),
        path_key: key,
        name: name.into(),
    }
}

pub fn fixed_configuration() -> (StableItemId, DescriptorFixedConfiguration) {
    let owner = id("Machine", ItemKind::Configuration);
    let k = cell_field(&owner, 0, "k", CellWrapper::KCell, BuiltinSort::KSequence);
    let env = cell_field(&owner, 1, "env", CellWrapper::Cell, BuiltinSort::Map);
    let configuration = DescriptorFixedConfiguration {
        root: DescriptorConfigurationRoot::GeneratedTop,
        declaration: DescriptorConfigurationDeclaration {
            key: key(ProvenanceRole::ConfigurationDeclaration, 0),
            fields: vec![k.clone(), env.clone()],
        },
        initializer: DescriptorConfigurationInitializer {
            key: key(ProvenanceRole::InitializerDeclaration, 0),
            owner_key: key(ProvenanceRole::InitializerResultType, 0),
            owner: owner.clone(),
            variables: vec![
                initializer_variable(0, "pgm", "PGM", BuiltinSort::Id, true),
                initializer_variable(1, "env", "ENV", BuiltinSort::Map, false),
            ],
            body_key: key(ProvenanceRole::InitializerBody, 0),
            cells: vec![
                DescriptorInitializerCell {
                    key: key(ProvenanceRole::InitializerCell, 0),
                    field: DescriptorCellReference {
                        key: key(ProvenanceRole::InitializerField, 0),
                        cell: k.reference.cell,
                    },
                    content: ProtocolInitializerCellContent::Leaf {
                        constructor_key: key(ProvenanceRole::InitializerCellConstructor, 0),
                        wrapper: CellWrapper::KCell,
                        value: ProtocolInitializerStateTerm::KSequence(ProtocolKSequence {
                            payload_key: Some(key(ProvenanceRole::KSequencePayload, 0)),
                            dot_k_key: None,
                            notation: krs_ir::DescriptorKSequenceNotation::Comma,
                            items: vec![ProtocolKSequenceItem {
                                key: key(ProvenanceRole::KSequenceItem, 0),
                                value: ProtocolInitializerTerm {
                                    key: key(ProvenanceRole::InitializerTerm, 0),
                                    term: variable(ProvenanceRole::InitializerTermPath, 0, "pgm"),
                                },
                            }],
                        }),
                    },
                },
                DescriptorInitializerCell {
                    key: key(ProvenanceRole::InitializerCell, 1),
                    field: DescriptorCellReference {
                        key: key(ProvenanceRole::InitializerField, 1),
                        cell: env.reference.cell,
                    },
                    content: ProtocolInitializerCellContent::Leaf {
                        constructor_key: key(ProvenanceRole::InitializerCellConstructor, 1),
                        wrapper: CellWrapper::Cell,
                        value: ProtocolInitializerStateTerm::Term(ProtocolInitializerTerm {
                            key: key(ProvenanceRole::InitializerTerm, 1),
                            term: variable(ProvenanceRole::InitializerTermPath, 1, "env"),
                        }),
                    },
                },
            ],
        },
    };
    (owner, configuration)
}

pub fn rule_cell(
    owner: &StableItemId,
    side: RuleSide,
    ordinal: u32,
    name: &str,
    wrapper: CellWrapper,
    value: ProtocolRuleStateTerm<DescriptorTerm>,
) -> ProtocolRuleCell<DescriptorCellReference, DescriptorTerm> {
    ProtocolRuleCell {
        field: DescriptorCellReference {
            key: key(
                side_role(
                    side,
                    ProvenanceRole::RuleLeftCellsField,
                    ProvenanceRole::RuleRightCellsField,
                ),
                ordinal,
            ),
            cell: DescriptorCellIdentity {
                owner: owner.clone(),
                field: name.into(),
            },
        },
        wrapper_key: Some(key(
            side_role(
                side,
                ProvenanceRole::RuleLeftCellsWrapper,
                ProvenanceRole::RuleRightCellsWrapper,
            ),
            ordinal,
        )),
        wrapper: Some(wrapper),
        value,
    }
}

pub fn side_role(side: RuleSide, left: ProvenanceRole, right: ProvenanceRole) -> ProvenanceRole {
    match side {
        RuleSide::Left => left,
        RuleSide::Right => right,
    }
}

pub fn term_binding(name: &str, ordinal: u32, sort: DescriptorSortRef) -> DescriptorRuleBinding {
    ProtocolRuleBinding {
        name: name.into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: sort_ref(ProvenanceRole::RuleBindingType, ordinal, sort),
        },
    }
}

pub fn frame_binding(
    name: &str,
    kind: ProtocolRuleBindingKind<DescriptorSortReference>,
) -> DescriptorRuleBinding {
    ProtocolRuleBinding {
        name: name.into(),
        kind,
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Builds both sides and provenance of the configuration rule fixture together."
)]
pub fn configuration_rule(owner: &StableItemId) -> DescriptorConfigurationRule {
    let k_state = |side: RuleSide, value: &str, tail| {
        ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
            payload_key: Some(key(
                side_role(
                    side,
                    ProvenanceRole::RuleLeftKSequencePayload,
                    ProvenanceRole::RuleRightKSequencePayload,
                ),
                0,
            )),
            dot_k_key: None,
            notation: krs_ir::DescriptorKSequenceNotation::Comma,
            items: vec![ProtocolRuleKSequenceItem {
                key: key(
                    side_role(
                        side,
                        ProvenanceRole::RuleLeftKSequenceItem,
                        ProvenanceRole::RuleRightKSequenceItem,
                    ),
                    0,
                ),
                value: variable(
                    side_role(
                        side,
                        ProvenanceRole::RuleLeftReference,
                        ProvenanceRole::RuleRightReference,
                    ),
                    0,
                    value,
                ),
            }],
            tail,
        })
    };
    DescriptorConfigurationRule {
        sentence_kind: krs_ir::ConfigurationSentenceKind::Transition,
        label: None,
        priority: None,
        nondet: None,
        requires: None,
        claim: None,
        pattern_key: key(ProvenanceRole::RulePattern, 0),
        subject_configuration: DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleType, 0),
            configuration: owner.clone(),
        },
        result_key: Some(key(ProvenanceRole::RuleResult, 0)),
        result_configuration: Some(DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleResultType, 0),
            configuration: owner.clone(),
        }),
        bindings: vec![
            term_binding("X", 0, DescriptorSortRef::Builtin(BuiltinSort::Id)),
            frame_binding("tail", ProtocolRuleBindingKind::KSequenceFrame),
            term_binding(
                "V",
                1,
                DescriptorSortRef::Declared(id("Value", ItemKind::Sort)),
            ),
            frame_binding("rest", ProtocolRuleBindingKind::MapFrame),
            frame_binding("state", ProtocolRuleBindingKind::ConfigurationFrame),
        ],
        subject: DescriptorRuleCells {
            key: key(ProvenanceRole::RuleLeftCellsPayload, 0),
            cells: vec![
                rule_cell(
                    owner,
                    RuleSide::Left,
                    0,
                    "k",
                    CellWrapper::KCell,
                    k_state(
                        RuleSide::Left,
                        "X",
                        ProtocolRuleFrame::Bind {
                            key: key(ProvenanceRole::RuleLeftKSequenceTail, 0),
                            binding: "tail".into(),
                        },
                    ),
                ),
                rule_cell(
                    owner,
                    RuleSide::Left,
                    1,
                    "env",
                    CellWrapper::Cell,
                    ProtocolRuleStateTerm::Map(ProtocolRuleMap {
                        payload_key: Some(key(ProvenanceRole::RuleLeftMapPayload, 0)),
                        body: ProtocolRuleMapBody::Items {
                            items: vec![ProtocolRuleMapItem {
                                key_key: key(ProvenanceRole::RuleLeftMapKey, 0),
                                key: variable(ProvenanceRole::RuleLeftReference, 1, "X"),
                                value_key: key(ProvenanceRole::RuleLeftMapValue, 0),
                                value: variable(ProvenanceRole::RuleLeftReference, 2, "V"),
                            }],
                            remainder: ProtocolRuleFrame::Bind {
                                key: key(ProvenanceRole::RuleLeftMapRemainder, 0),
                                binding: "rest".into(),
                            },
                        },
                    }),
                ),
            ],
            remainder: ProtocolRuleFrame::Bind {
                key: key(ProvenanceRole::RuleLeftCellsRemainder, 0),
                binding: "state".into(),
            },
        },
        result: Some(DescriptorRuleCells {
            key: key(ProvenanceRole::RuleRightCellsPayload, 0),
            cells: vec![rule_cell(
                owner,
                RuleSide::Right,
                0,
                "k",
                CellWrapper::KCell,
                k_state(
                    RuleSide::Right,
                    "V",
                    ProtocolRuleFrame::Reuse {
                        key: key(ProvenanceRole::RuleRightKSequenceTail, 0),
                        binding: "tail".into(),
                    },
                ),
            )],
            remainder: ProtocolRuleFrame::Reuse {
                key: key(ProvenanceRole::RuleRightCellsRemainder, 0),
                binding: "state".into(),
            },
        }),
        existentials: Vec::new(),
        ensures: None,
        fresh: Vec::new(),
        evaluation: None,
    }
}

pub fn descriptor(id: StableItemId, payload: DescriptorPayload) -> DescriptorInputs {
    let keys = match &payload {
        DescriptorPayload::Sort(_) => vec![key(ProvenanceRole::SortDeclaration, 0)],
        DescriptorPayload::FixedConfiguration(configuration) => configuration
            .expected_provenance_keys(&id)
            .unwrap()
            .into_iter()
            .collect(),
        DescriptorPayload::ConfigurationRule(rule) => rule
            .expected_provenance_keys(id.item_kind())
            .unwrap()
            .into_iter()
            .collect(),
        _ => unreachable!(),
    };
    let primary = match payload {
        DescriptorPayload::Sort(_) => key(ProvenanceRole::SortDeclaration, 0),
        DescriptorPayload::FixedConfiguration(_) => {
            key(ProvenanceRole::ConfigurationDeclaration, 0)
        }
        DescriptorPayload::ConfigurationRule(_) => key(ProvenanceRole::RuleDeclaration, 0),
        _ => unreachable!(),
    };
    DescriptorInputs::new(id, BTreeMap::new(), provenance(primary, keys), payload)
}

pub fn bundle() -> DescriptorBundleInputs {
    let (owner, configuration) = fixed_configuration();
    let rule = configuration_rule(&owner);
    DescriptorBundleInputs::new(vec![
        descriptor(
            framework_kitem(),
            DescriptorPayload::Sort(SortDescriptor {
                parents: BTreeSet::new(),
            }),
        ),
        descriptor(
            id("Value", ItemKind::Sort),
            DescriptorPayload::Sort(SortDescriptor {
                parents: BTreeSet::new(),
            }),
        ),
        descriptor(
            owner,
            DescriptorPayload::FixedConfiguration(Box::new(configuration)),
        ),
        descriptor(
            id("var", ItemKind::Rule),
            DescriptorPayload::ConfigurationRule(Box::new(rule)),
        ),
    ])
}
