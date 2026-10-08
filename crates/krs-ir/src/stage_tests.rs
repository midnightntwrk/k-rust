//! Traversal coverage for collector configuration, rule, and payload shapes.

use crate::stage::tests::CountingMap;
use crate::transport::{configuration as cfg, rule};
use crate::{
    BuiltinSort, ConstructorDescriptor, ConstructorFieldDescriptor, DescriptorCellDeclaration,
    DescriptorCellDeclarationReference, DescriptorCellField, DescriptorCellIdentity,
    DescriptorCellReference, DescriptorClaim, DescriptorClaimBinder,
    DescriptorConfigurationInitializer, DescriptorConfigurationReference,
    DescriptorConfigurationRule, DescriptorConfigurationVariable, DescriptorContextAlias,
    DescriptorFixedConfiguration, DescriptorHeadRule, DescriptorInitializerCell,
    DescriptorInitializerStateTerm, DescriptorPayload, DescriptorRuleCells,
    DescriptorRuleCondition, DescriptorSortRef, DescriptorSortReference, DescriptorStage,
    DescriptorTerm, GrammarDescriptor, ItemKind, PackageId, ProvenanceKey, ProvenanceRole, RefMap,
    SentenceKind, SortDescriptor, StableItemId, StructuredRuleDescriptor,
};

macro_rules! assert_mapping {
    ($value:expr, [$($callback:ident),*], [$($call:literal),* $(,)?]) => {{
        let value = $value;
        let expected_calls: &[&'static str] = &[$($call),*];
        let mut map = CountingMap::default();
        let mapped = value.clone().try_map_refs(&mut map $(, &mut $callback)*).unwrap();
        assert_eq!(mapped, value);
        assert_eq!(map.calls, expected_calls);
        for (index, failure) in expected_calls.iter().copied().enumerate() {
            if expected_calls[..index].contains(&failure) {
                continue;
            }
            let mut failing = CountingMap {
                fail: Some(failure),
                ..CountingMap::default()
            };
            let error = value.clone().try_map_refs(&mut failing $(, &mut $callback)*).unwrap_err();
            assert_eq!(error, failure);
            assert_eq!(failing.calls, expected_calls[..=index]);
        }
    }};
}

fn key(ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(ProvenanceRole::RulePattern, ordinal)
}

fn item(kind: ItemKind, name: &str) -> StableItemId {
    let package = PackageId::new("ORG-EXAMPLE-TRAVERSAL", "test", "0.1.0", "workspace").unwrap();
    StableItemId::new(package, ["transport"], name, kind, "").unwrap()
}

fn sort(ordinal: u32) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(ordinal),
        sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
    }
}

fn term(ordinal: u32) -> DescriptorTerm {
    DescriptorTerm::Anonymous {
        key: key(ordinal),
        sort: sort(ordinal),
        spelling: "_".to_owned(),
    }
}

fn cell(ordinal: u32) -> DescriptorCellReference {
    DescriptorCellReference {
        key: key(ordinal),
        cell: DescriptorCellIdentity {
            owner: item(ItemKind::Configuration, "State"),
            field: format!("field{ordinal}"),
        },
    }
}

fn cell_declaration(ordinal: u32) -> DescriptorCellDeclarationReference {
    DescriptorCellDeclarationReference {
        key: key(ordinal),
        declaration: item(ItemKind::Cell, "Nested"),
    }
}

fn configuration(ordinal: u32) -> DescriptorConfigurationReference {
    DescriptorConfigurationReference {
        key: key(ordinal),
        configuration: item(ItemKind::Configuration, "State"),
    }
}

fn map_sort(
    value: DescriptorSortReference,
    map: &mut CountingMap,
) -> Result<DescriptorSortReference, &'static str> {
    <CountingMap as RefMap<DescriptorStage, DescriptorStage>>::sort(map, value)
}

fn map_term(value: DescriptorTerm, map: &mut CountingMap) -> Result<DescriptorTerm, &'static str> {
    value.try_map_refs(map)
}

fn map_cell(
    value: DescriptorCellReference,
    map: &mut CountingMap,
) -> Result<DescriptorCellReference, &'static str> {
    <CountingMap as RefMap<DescriptorStage, DescriptorStage>>::cell(map, value)
}

fn map_cell_declaration(
    value: DescriptorCellDeclarationReference,
    map: &mut CountingMap,
) -> Result<DescriptorCellDeclarationReference, &'static str> {
    <CountingMap as RefMap<DescriptorStage, DescriptorStage>>::cell_declaration(map, value)
}

fn map_owner(value: StableItemId, map: &mut CountingMap) -> Result<StableItemId, &'static str> {
    <CountingMap as RefMap<DescriptorStage, DescriptorStage>>::initializer_owner(map, value)
}

fn variable() -> DescriptorConfigurationVariable {
    DescriptorConfigurationVariable {
        binding_key: key(0),
        binding: "input".to_owned(),
        external_name_key: key(1),
        external_name: "INPUT".to_owned(),
        sort: sort(2),
        main_key: Some(key(3)),
    }
}

fn map_variable(
    value: DescriptorConfigurationVariable,
    map: &mut CountingMap,
) -> Result<DescriptorConfigurationVariable, &'static str> {
    value.try_map_refs(map, &mut map_sort)
}

fn initializer_term(ordinal: u32) -> cfg::ProtocolInitializerTerm<DescriptorTerm> {
    cfg::ProtocolInitializerTerm {
        key: key(ordinal),
        term: term(ordinal),
    }
}

fn map_initializer_state(
    value: DescriptorInitializerStateTerm,
    map: &mut CountingMap,
) -> Result<DescriptorInitializerStateTerm, &'static str> {
    value.try_map_refs(map, &mut map_term)
}

fn initializer_cell(ordinal: u32) -> DescriptorInitializerCell {
    DescriptorInitializerCell {
        key: key(ordinal),
        field: cell(ordinal),
        content: cfg::ProtocolInitializerCellContent::Leaf {
            constructor_key: key(ordinal + 1),
            wrapper: cfg::CellWrapper::Cell,
            value: cfg::ProtocolInitializerStateTerm::Term(initializer_term(ordinal + 2)),
        },
    }
}

fn map_initializer_cell(
    value: DescriptorInitializerCell,
    map: &mut CountingMap,
) -> Result<DescriptorInitializerCell, &'static str> {
    value.try_map_refs(
        map,
        &mut map_cell,
        &mut map_cell_declaration,
        &mut map_initializer_state,
    )
}

fn field(
    ordinal: u32,
    content: cfg::ProtocolCellContent<DescriptorSortReference, DescriptorCellDeclarationReference>,
) -> DescriptorCellField {
    DescriptorCellField {
        reference: cell(ordinal),
        rust_field: format!("field{ordinal}"),
        emitted_name: Some(cfg::DescriptorCellName {
            key: key(ordinal),
            value: "renamed".to_owned(),
        }),
        color: Some(cfg::DescriptorCellColor {
            key: key(ordinal),
            value: "blue".to_owned(),
        }),
        multiplicity: None,
        cell_type: None,
        content,
    }
}

fn map_field(
    value: DescriptorCellField,
    map: &mut CountingMap,
) -> Result<DescriptorCellField, &'static str> {
    value.try_map_refs(map, &mut map_cell, &mut map_sort, &mut map_cell_declaration)
}

fn declaration() -> DescriptorCellDeclaration {
    cfg::ProtocolCellDeclaration {
        key: key(0),
        fields: vec![
            field(
                1,
                cfg::ProtocolCellContent::Leaf {
                    wrapper_key: key(2),
                    wrapper: cfg::CellWrapper::Cell,
                    sort: sort(3),
                    arguments: vec![sort(4), sort(5)],
                },
            ),
            field(
                6,
                cfg::ProtocolCellContent::Nested {
                    declaration: cell_declaration(7),
                },
            ),
        ],
    }
}

fn initializer() -> DescriptorConfigurationInitializer {
    DescriptorConfigurationInitializer {
        key: key(0),
        owner_key: key(1),
        owner: item(ItemKind::Configuration, "State"),
        variables: vec![variable()],
        body_key: key(2),
        cells: vec![DescriptorInitializerCell {
            key: key(3),
            field: cell(4),
            content: cfg::ProtocolInitializerCellContent::Nested {
                declaration: cell_declaration(5),
                children: vec![initializer_cell(6)],
            },
        }],
    }
}

fn fixed_configuration() -> DescriptorFixedConfiguration {
    DescriptorFixedConfiguration {
        root: cfg::DescriptorConfigurationRoot::Named {
            key: key(0),
            name: "top".to_owned(),
        },
        declaration: declaration(),
        initializer: initializer(),
    }
}

#[test]
fn configuration_declaration_traversal_maps_fields_and_generic_arguments() {
    let value = declaration();
    assert_mapping!(
        value.fields[0].content.clone(),
        [map_sort, map_cell_declaration],
        ["sort", "sort", "sort"]
    );
    assert_mapping!(
        value.fields[1].content.clone(),
        [map_sort, map_cell_declaration],
        ["cell_declaration"]
    );
    assert_mapping!(
        value.fields[0].clone(),
        [map_cell, map_sort, map_cell_declaration],
        ["sort", "sort", "sort", "cell"]
    );
    assert_mapping!(
        value,
        [map_field],
        ["sort", "sort", "sort", "cell", "cell_declaration", "cell"]
    );
    assert_mapping!(variable(), [map_sort], ["sort"]);
}

#[test]
fn initializer_state_traversal_maps_sequences_and_every_map_variant() {
    assert_mapping!(initializer_term(0), [map_term], ["sort"]);
    let sequence = cfg::ProtocolKSequence {
        payload_key: Some(key(0)),
        dot_k_key: None,
        notation: cfg::DescriptorKSequenceNotation::Operator,
        items: vec![cfg::ProtocolKSequenceItem {
            key: key(1),
            value: initializer_term(2),
        }],
    };
    assert_mapping!(sequence.items[0].clone(), [map_term], ["sort"]);
    assert_mapping!(sequence.clone(), [map_term], ["sort"]);
    assert_mapping!(
        cfg::ProtocolInitializerStateTerm::KSequence(sequence),
        [map_term],
        ["sort"]
    );
    assert_mapping!(
        cfg::ProtocolInitializerStateTerm::Term(initializer_term(0)),
        [map_term],
        ["sort"]
    );
    let entry = cfg::ProtocolMapItem {
        key_key: key(0),
        key: initializer_term(1),
        value_key: key(2),
        value: initializer_term(3),
    };
    assert_mapping!(entry.clone(), [map_term], ["sort", "sort"]);
    let bodies = [
        cfg::ProtocolMapBody::Empty { explicit_dot: true },
        cfg::ProtocolMapBody::Items { items: vec![entry] },
        cfg::ProtocolMapBody::Update {
            base_key: key(0),
            base: initializer_term(1),
            key_key: key(2),
            key: initializer_term(3),
            value_key: key(4),
            value: initializer_term(5),
        },
    ];
    for body in bodies {
        let expected = match &body {
            cfg::ProtocolMapBody::Empty { .. } => 0,
            cfg::ProtocolMapBody::Items { .. } => 2,
            cfg::ProtocolMapBody::Update { .. } => 3,
        };
        let mut map = CountingMap::default();
        let mapped = body.clone().try_map_refs(&mut map, &mut map_term).unwrap();
        assert_eq!(mapped, body);
        assert_eq!(map.calls, vec!["sort"; expected]);
        let state = cfg::ProtocolInitializerStateTerm::Map(cfg::ProtocolMap {
            payload_key: Some(key(0)),
            body,
        });
        let mut map = CountingMap::default();
        assert_eq!(
            state.clone().try_map_refs(&mut map, &mut map_term).unwrap(),
            state
        );
        assert_eq!(map.calls, vec!["sort"; expected]);
        if expected > 0 {
            let mut failing = CountingMap {
                fail: Some("sort"),
                ..CountingMap::default()
            };
            assert_eq!(
                state.try_map_refs(&mut failing, &mut map_term).unwrap_err(),
                "sort"
            );
            assert_eq!(failing.calls, ["sort"]);
        }
    }
}

#[test]
fn recursive_initializer_and_fixed_configuration_traversals_short_circuit() {
    assert_mapping!(
        initializer_cell(0).content,
        [map_cell, map_cell_declaration, map_initializer_state],
        ["sort"]
    );
    assert_mapping!(
        initializer_cell(0),
        [map_cell, map_cell_declaration, map_initializer_state],
        ["sort", "cell"]
    );
    assert_mapping!(
        initializer().cells[0].content.clone(),
        [map_cell, map_cell_declaration, map_initializer_state],
        ["cell_declaration", "sort", "cell"]
    );
    assert_mapping!(
        initializer(),
        [map_owner, map_variable, map_initializer_cell],
        [
            "initializer_owner",
            "sort",
            "cell_declaration",
            "sort",
            "cell",
            "cell"
        ]
    );
    assert_mapping!(
        fixed_configuration(),
        [],
        [
            "sort",
            "sort",
            "sort",
            "cell",
            "cell_declaration",
            "cell",
            "initializer_owner",
            "sort",
            "cell_declaration",
            "sort",
            "cell",
            "cell"
        ]
    );
}

fn frames() -> [rule::ProtocolRuleFrame; 4] {
    [
        rule::ProtocolRuleFrame::Exact,
        rule::ProtocolRuleFrame::Anonymous { key: key(0) },
        rule::ProtocolRuleFrame::Bind {
            key: key(1),
            binding: "rest".to_owned(),
        },
        rule::ProtocolRuleFrame::Reuse {
            key: key(2),
            binding: "rest".to_owned(),
        },
    ]
}

fn rule_cells() -> DescriptorRuleCells {
    DescriptorRuleCells {
        key: key(0),
        cells: vec![rule::ProtocolRuleCell {
            field: cell(1),
            wrapper_key: key(2),
            wrapper: cfg::CellWrapper::Cell,
            value: rule::ProtocolRuleStateTerm::Term(term(3)),
        }],
        remainder: rule::ProtocolRuleFrame::Bind {
            key: key(4),
            binding: "state".to_owned(),
        },
    }
}

fn binder(ordinal: u32) -> DescriptorClaimBinder {
    DescriptorClaimBinder {
        declaration_key: key(ordinal),
        name_key: key(ordinal + 1),
        name: format!("binding{ordinal}"),
        sort: sort(ordinal + 2),
    }
}

fn claim() -> DescriptorClaim {
    DescriptorClaim {
        declaration_key: key(0),
        modality_key: key(1),
        modality: rule::ClaimModality::OnePath,
        circularity_key: Some(key(2)),
        universals: vec![binder(3)],
        existentials: vec![binder(4)],
        ensures: Some(DescriptorRuleCondition {
            key: key(5),
            term: term(6),
        }),
        or_bool_keys: vec![key(7)],
    }
}

fn context_alias() -> DescriptorContextAlias {
    DescriptorContextAlias {
        declaration_key: key(0),
        name_key: key(1),
        name: "context".to_owned(),
        here_key: key(2),
        here: "value".to_owned(),
        pattern_key: key(3),
        configuration: configuration(4),
        bindings: vec![
            rule::ProtocolContextAliasBinding {
                name: "value".to_owned(),
                kind: rule::ProtocolContextAliasBindingKind::Here,
            },
            rule::ProtocolContextAliasBinding {
                name: "other".to_owned(),
                kind: rule::ProtocolContextAliasBindingKind::Term { sort: sort(5) },
            },
        ],
        pattern: rule_cells(),
    }
}

fn configuration_rule() -> DescriptorConfigurationRule {
    DescriptorConfigurationRule {
        sentence_kind: crate::ConfigurationSentenceKind::Claim,
        label: None,
        priority: None,
        nondet: None,
        requires: Some(DescriptorRuleCondition {
            key: key(0),
            term: term(1),
        }),
        claim: Some(claim()),
        pattern_key: key(2),
        subject_configuration: configuration(3),
        result_key: key(4),
        result_configuration: configuration(5),
        bindings: vec![rule::ProtocolRuleBinding {
            name: "value".to_owned(),
            kind: rule::ProtocolRuleBindingKind::Term { sort: sort(6) },
        }],
        subject: rule_cells(),
        result: rule_cells(),
    }
}

#[test]
fn rule_and_context_bindings_traverse_only_term_sorts() {
    let binding = rule::ProtocolRuleBinding {
        name: "value".to_owned(),
        kind: rule::ProtocolRuleBindingKind::Term { sort: sort(0) },
    };
    assert_mapping!(binding.kind.clone(), [map_sort], ["sort"]);
    assert_mapping!(binding, [map_sort], ["sort"]);
    for kind in [
        rule::ProtocolRuleBindingKind::KSequenceFrame,
        rule::ProtocolRuleBindingKind::MapFrame,
        rule::ProtocolRuleBindingKind::ConfigurationFrame,
    ] {
        assert_mapping!(kind, [map_sort], []);
    }
    let binding = rule::ProtocolContextAliasBinding {
        name: "other".to_owned(),
        kind: rule::ProtocolContextAliasBindingKind::Term { sort: sort(1) },
    };
    assert_mapping!(binding.kind.clone(), [map_sort], ["sort"]);
    assert_mapping!(binding, [map_sort], ["sort"]);
    for kind in [
        rule::ProtocolContextAliasBindingKind::Here,
        rule::ProtocolContextAliasBindingKind::KSequenceFrame,
        rule::ProtocolContextAliasBindingKind::MapFrame,
        rule::ProtocolContextAliasBindingKind::ConfigurationFrame,
    ] {
        assert_mapping!(kind, [map_sort], []);
    }
}

#[test]
fn rule_sequence_traversal_preserves_every_frame_variant() {
    let sequence_item = rule::ProtocolRuleKSequenceItem {
        key: key(0),
        value: term(1),
    };
    assert_mapping!(sequence_item.clone(), [map_term], ["sort"]);
    for tail in frames() {
        let sequence = rule::ProtocolRuleKSequence {
            payload_key: Some(key(0)),
            dot_k_key: None,
            notation: cfg::DescriptorKSequenceNotation::Operator,
            items: vec![sequence_item.clone()],
            tail,
        };
        assert_mapping!(sequence.clone(), [map_term], ["sort"]);
        assert_mapping!(
            rule::ProtocolRuleStateTerm::KSequence(sequence),
            [map_term],
            ["sort"]
        );
    }
}

#[test]
fn rule_map_traversal_covers_items_updates_empty_and_frames() {
    let entry = rule::ProtocolRuleMapItem {
        key_key: key(0),
        key: term(1),
        value_key: key(2),
        value: term(3),
    };
    assert_mapping!(entry.clone(), [map_term], ["sort", "sort"]);
    for remainder in frames() {
        let body = rule::ProtocolRuleMapBody::Items {
            items: vec![entry.clone()],
            remainder,
        };
        assert_mapping!(body.clone(), [map_term], ["sort", "sort"]);
        let map = rule::ProtocolRuleMap {
            payload_key: Some(key(0)),
            body,
        };
        assert_mapping!(map.clone(), [map_term], ["sort", "sort"]);
        assert_mapping!(
            rule::ProtocolRuleStateTerm::Map(map),
            [map_term],
            ["sort", "sort"]
        );
    }
    let update = rule::ProtocolRuleMapBody::Update {
        base_key: key(0),
        base: term(1),
        key_key: key(2),
        key: term(3),
        value_key: key(4),
        value: term(5),
    };
    assert_mapping!(update, [map_term], ["sort", "sort", "sort"]);
    assert_mapping!(
        rule::ProtocolRuleMapBody::Empty { explicit_dot: true },
        [map_term],
        []
    );
}

#[test]
fn rule_cells_traversal_maps_fields_and_preserves_configuration_frames() {
    let value = rule_cells().cells.remove(0);
    assert_mapping!(value.value.clone(), [map_term], ["sort"]);
    assert_mapping!(value.clone(), [map_cell, map_term], ["cell", "sort"]);
    for remainder in frames() {
        let cells = DescriptorRuleCells {
            key: key(0),
            cells: vec![value.clone()],
            remainder,
        };
        assert_mapping!(cells, [map_cell, map_term], ["cell", "sort"]);
    }
}

#[test]
fn claim_context_and_configuration_rule_traversals_visit_all_references() {
    assert_mapping!(binder(0), [], ["sort"]);
    assert_mapping!(claim(), [], ["sort", "sort", "sort"]);
    assert_mapping!(
        context_alias(),
        [],
        ["configuration", "sort", "cell", "sort"]
    );
    assert_mapping!(
        configuration_rule(),
        [],
        [
            "sort",
            "sort",
            "sort",
            "sort",
            "configuration",
            "configuration",
            "sort",
            "cell",
            "sort",
            "cell",
            "sort"
        ]
    );
}

fn head_rule() -> DescriptorHeadRule {
    DescriptorHeadRule {
        sentence_kind: SentenceKind::Transition,
        label: None,
        priority: None,
        nondet: None,
        pattern_key: key(0),
        result_key: key(1),
        head_sort: None,
        configuration: item(ItemKind::Configuration, "State"),
        computation_cell: cell(2),
        bindings: Vec::new(),
        subject: term(3),
        result: crate::DescriptorHeadRuleResult::Replace(term(4)),
        requires: None,
        extras: Vec::new(),
    }
}

fn map_head(
    value: DescriptorHeadRule,
    map: &mut CountingMap,
) -> Result<DescriptorHeadRule, &'static str> {
    value.try_map_refs(map)
}

fn structured_rule() -> StructuredRuleDescriptor {
    StructuredRuleDescriptor {
        sentence_kind: SentenceKind::Transition,
        label: None,
        requires: Some(DescriptorRuleCondition {
            key: key(0),
            term: term(1),
        }),
        priority: None,
        nondet: None,
        anywhere: None,
        simplification: None,
        pattern_key: key(2),
        result_key: key(3),
        subject_sort: sort(4),
        result_sort: sort(5),
        bindings: vec!["value".to_owned()],
        subject: term(6),
        result: term(7),
    }
}

#[test]
fn sort_and_constructor_traversals_preserve_variant_data() {
    let sorts = SortDescriptor {
        parents: [
            item(ItemKind::Sort, "First"),
            item(ItemKind::Sort, "Second"),
        ]
        .into_iter()
        .collect(),
    };
    assert_mapping!(sorts.clone(), [], ["parent", "parent"]);
    let constructor = ConstructorDescriptor {
        sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
        fields: vec![
            ConstructorFieldDescriptor {
                name: "first".to_owned(),
                sort: Some(DescriptorSortRef::Builtin(BuiltinSort::Int)),
            },
            ConstructorFieldDescriptor {
                name: "second".to_owned(),
                sort: None,
            },
        ],
    };
    assert_mapping!(
        constructor.fields[0].clone(),
        [],
        ["constructor_field_sort"]
    );
    assert_mapping!(
        constructor.clone(),
        [],
        [
            "constructor_sort",
            "constructor_field_sort",
            "constructor_field_sort"
        ]
    );
}

#[test]
fn declaration_payload_traversal_maps_references_and_propagates_errors() {
    let sorts = SortDescriptor {
        parents: [
            item(ItemKind::Sort, "First"),
            item(ItemKind::Sort, "Second"),
        ]
        .into_iter()
        .collect(),
    };
    let constructor = ConstructorDescriptor {
        sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
        fields: vec![
            ConstructorFieldDescriptor {
                name: "first".to_owned(),
                sort: Some(DescriptorSortRef::Builtin(BuiltinSort::Int)),
            },
            ConstructorFieldDescriptor {
                name: "second".to_owned(),
                sort: None,
            },
        ],
    };
    assert_mapping!(
        DescriptorPayload::Sort(sorts),
        [map_head],
        ["parent", "parent"]
    );
    assert_mapping!(
        DescriptorPayload::Constructor(constructor),
        [map_head],
        [
            "constructor_sort",
            "constructor_field_sort",
            "constructor_field_sort"
        ]
    );
    assert_mapping!(
        DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
            key: key(0),
            subsort: sort(1),
            supersort: sort(2)
        })),
        [map_head],
        ["sort", "sort"]
    );
    assert_mapping!(
        DescriptorPayload::StructuredRule(Box::new(structured_rule())),
        [map_head],
        ["sort", "sort", "sort", "sort", "sort"]
    );
}

#[test]
fn configuration_payload_traversal_maps_references_and_propagates_errors() {
    assert_mapping!(
        DescriptorPayload::FixedConfiguration(Box::new(fixed_configuration())),
        [map_head],
        [
            "sort",
            "sort",
            "sort",
            "cell",
            "cell_declaration",
            "cell",
            "initializer_owner",
            "sort",
            "cell_declaration",
            "sort",
            "cell",
            "cell"
        ]
    );
    assert_mapping!(
        DescriptorPayload::Cell(Box::new(declaration())),
        [map_head],
        ["sort", "sort", "sort", "cell", "cell_declaration", "cell"]
    );
    assert_mapping!(
        DescriptorPayload::ConfigurationRule(Box::new(configuration_rule())),
        [map_head],
        [
            "sort",
            "sort",
            "sort",
            "sort",
            "configuration",
            "configuration",
            "sort",
            "cell",
            "sort",
            "cell",
            "sort"
        ]
    );
    assert_mapping!(
        DescriptorPayload::HeadRule(Box::new(head_rule())),
        [map_head],
        ["item", "cell", "sort", "sort"]
    );
    assert_mapping!(
        DescriptorPayload::ContextAlias(Box::new(context_alias())),
        [map_head],
        ["configuration", "sort", "cell", "sort"]
    );
}

#[test]
fn host_transport_references_remain_process_local() {
    static_assertions::assert_not_impl_any!(crate::HostTerm: serde::Serialize, serde::de::DeserializeOwned);
    static_assertions::assert_not_impl_any!(crate::HostDescriptorPayload: serde::Serialize, serde::de::DeserializeOwned);
    static_assertions::assert_not_impl_any!(crate::HostHeadRule: serde::Serialize, serde::de::DeserializeOwned);
}
