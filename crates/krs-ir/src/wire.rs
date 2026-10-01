//! Indexed, unresolved host payloads emitted as static macro data.

use serde::{Deserialize, Serialize};

use crate::stage::{WireStage, stage_shape};
use crate::transport::configuration::{
    FixedConfiguration, ProtocolCellContent, ProtocolCellField, ProtocolConfigurationVariable,
    ProtocolInitializerCell, ProtocolInitializerStateTerm, StageCellDeclaration,
    StageConfigurationInitializer,
};
use crate::transport::grammar::{
    CellTermField, Production, ProductionAttribute, ProductionItem, ProductionOwner, RuleCondition,
    StageGrammarDescriptor, StructuredRule, Term, TermArgument,
};
use crate::transport::head_rule::HeadRule;
use crate::transport::rule::{
    Claim, ClaimBinder, ConfigurationRule, ContextAlias, ProtocolRuleCells, ProtocolRuleKSequence,
    ProtocolRuleMap, ProtocolRuleStateTerm,
};
use crate::{
    ProtocolHeadRuleBinding, ProtocolHeadRuleExtra, ProtocolHeadRuleResult, ProvenanceKey,
};

/// Index into the static host type-key table.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(transparent)]
pub struct TypeSlot(pub usize);

/// Index into the static host item-identity table.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ItemSlot(pub usize);

/// Index into the static host application-target table.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(transparent)]
pub struct TargetSlot(pub usize);

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireTypeReference {
    pub slot: TypeSlot,
    pub authored_path: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireSortReference {
    pub key: ProvenanceKey,
    pub target: WireTypeReference,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireConfigurationReference {
    pub key: ProvenanceKey,
    pub configuration: WireTypeReference,
}

/// Indexed Rust owner and generated field-marker identities.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireCellIdentity {
    pub owner: TypeSlot,
    pub field: TypeSlot,
}

/// Static selected-cell occurrence with provenance.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireCellReference {
    pub key: ProvenanceKey,
    pub cell: WireCellIdentity,
}

/// Static nominal nested-cell occurrence with provenance.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireCellDeclarationReference {
    pub key: ProvenanceKey,
    pub declaration: WireTypeReference,
}

stage_shape! {
    /// Static indexed open-sort declaration.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "WireSortDescriptor",
        deny_unknown_fields,
        bound(serialize = "S::Parents: Serialize", deserialize = "S::Parents: Deserialize<'de>")
    )]
    pub struct StaticSort<S: Stage> {
        /// Direct super-sort references in authored order.
        pub parents: S::Parents => [parents],
    }
    host_shape: crate::HostSortDescriptor;
}

/// Static wire-stage sort declaration.
pub type WireSortDescriptor = StaticSort<WireStage>;
/// Static wire-stage cell declaration content.
pub type WireCellContent = ProtocolCellContent<WireSortReference, WireCellDeclarationReference>;
/// Static wire-stage fixed-cell field.
pub type WireCellField =
    ProtocolCellField<WireCellReference, WireSortReference, WireCellDeclarationReference>;
/// Static wire-stage fixed-cell declaration.
pub type WireCellDeclaration = StageCellDeclaration<WireStage>;
/// Static wire-stage configuration declaration.
pub type WireConfigurationDeclaration = StageCellDeclaration<WireStage>;
/// Static wire-stage configuration variable.
pub type WireConfigurationVariable = ProtocolConfigurationVariable<WireSortReference>;
/// Static wire-stage initializer state.
pub type WireInitializerStateTerm = ProtocolInitializerStateTerm<WireTerm>;
/// Static wire-stage initializer cell.
pub type WireInitializerCell = ProtocolInitializerCell<
    WireCellReference,
    WireCellDeclarationReference,
    WireInitializerStateTerm,
>;
/// Static wire-stage complete paired initializer.
pub type WireConfigurationInitializer = StageConfigurationInitializer<WireStage>;
/// Static wire-stage complete fixed configuration.
pub type WireFixedConfiguration = FixedConfiguration<WireStage>;
/// Static wire-stage configuration-rule cells.
pub type WireRuleCells = ProtocolRuleCells<WireCellReference, WireTerm>;
/// Static wire-stage configuration-rule state.
pub type WireRuleStateTerm = ProtocolRuleStateTerm<WireTerm>;
/// Static wire-stage configuration-rule K sequence.
pub type WireRuleKSequence = ProtocolRuleKSequence<WireTerm>;
/// Static wire-stage configuration-rule map.
pub type WireRuleMap = ProtocolRuleMap<WireTerm>;
/// Static wire-stage configuration rule or claim.
pub type WireConfigurationRule = ConfigurationRule<WireStage>;
/// Static wire-stage claim metadata.
pub type WireClaim = Claim<WireStage>;
/// Static wire-stage claim binder.
pub type WireClaimBinder = ClaimBinder<WireStage>;
/// Static wire-stage context alias.
pub type WireContextAlias = ContextAlias<WireStage>;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireApplicationReference {
    pub key: ProvenanceKey,
    pub target: TargetSlot,
    pub authored_path: String,
}

/// Static wire-stage form of [`TermArgument`].
pub type WireTermArgument = TermArgument<WireStage>;

/// Static wire-stage form of [`CellTermField`].
pub type WireCellTermField = CellTermField<WireStage>;

/// Static wire-stage form of [`Term`].
pub type WireTerm = Term<WireStage>;

/// Static wire-stage form of [`RuleCondition`].
pub type WireRuleCondition = RuleCondition<WireStage>;

/// Static wire-stage form of [`StructuredRule`].
pub type WireStructuredRule = StructuredRule<WireStage>;

stage_shape! {
    /// Static indexed constructor transport.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "WireConstructorFieldDescriptor",
        deny_unknown_fields,
        bound(
            serialize = "S::Sort: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Nominal: Deserialize<'de>"
        )
    )]
    pub struct StaticConstructorField<S: Stage> {
        /// Authored field name.
        pub name: String => [keep],
        /// Declared sort reference.
        pub sort: S::Nominal => [nominal],
    }
    host_shape: crate::HostConstructorFieldDescriptor;
}

/// Static wire-stage constructor transport.
pub type WireConstructorFieldDescriptor = StaticConstructorField<WireStage>;

stage_shape! {
    /// Static indexed constructor transport.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "WireConstructorDescriptor",
        deny_unknown_fields,
        bound(
            serialize = "S::Sort: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Nominal: Deserialize<'de>"
        )
    )]
    pub struct StaticConstructor<S: Stage> {
        /// Declared sort reference.
        pub sort: S::Sort => [sort],
        /// Constructor fields in authored order.
        pub fields: Vec<StaticConstructorField<S>> => [vec nested],
    }
    host_shape: crate::HostConstructorDescriptor;
}

/// Static wire-stage constructor transport.
pub type WireConstructorDescriptor = StaticConstructor<WireStage>;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireContextAliasReference {
    pub key: ProvenanceKey,
    pub slot: ItemSlot,
}

/// Static wire-stage form of [`ProductionItem`].
pub type WireProductionItem = ProductionItem<WireStage>;

/// Static wire-stage form of [`ProductionAttribute`].
pub type WireProductionAttribute = ProductionAttribute<WireStage>;

/// Static wire-stage form of [`ProductionOwner`].
pub type WireProductionOwner = ProductionOwner<WireStage>;

/// Static wire-stage form of [`Production`].
pub type WireProduction = Production<WireStage>;

/// Static wire-stage form of [`StageGrammarDescriptor`].
pub type WireGrammarDescriptor = StageGrammarDescriptor<WireStage>;

/// Static wire-stage binding in a readable head rule.
pub type WireHeadRuleBinding = ProtocolHeadRuleBinding<WireSortReference>;
/// Static wire-stage result in a readable head rule.
pub type WireHeadRuleResult = ProtocolHeadRuleResult<WireTerm>;
/// Static wire-stage extra-cell clause in a readable head rule.
pub type WireHeadRuleExtra = ProtocolHeadRuleExtra<WireHeadRuleCellReference, WireTerm>;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireHeadRuleCellReference {
    pub key: ProvenanceKey,
    pub name: String,
}

/// Static wire-stage form of [`HeadRule`].
pub type WireHeadRule = HeadRule<WireStage>;

/// Static indexed payload with an external wire envelope.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub enum WirePayload {
    /// Open-sort declaration.
    Sort(WireSortDescriptor),
    /// Constructor declaration.
    Constructor(WireConstructorDescriptor),
    /// Typed object-grammar sentence.
    Grammar(Box<WireGrammarDescriptor>),
    /// Fully structured relational sentence.
    StructuredRule(Box<WireStructuredRule>),
    /// Complete fixed configuration and initializer.
    FixedConfiguration(Box<WireFixedConfiguration>),
    /// Nominal nested fixed-cell declaration.
    Cell(Box<WireCellDeclaration>),
    /// Whole-configuration rule or claim.
    ConfigurationRule(Box<WireConfigurationRule>),
    /// Computation-head rule.
    HeadRule(Box<WireHeadRule>),
    /// Reusable fixed-configuration context template.
    ContextAlias(Box<WireContextAlias>),
}

#[cfg(test)]
mod tests {
    use super::{WireApplicationReference, WireTerm};
    use crate::{DescriptorApplicationHeadClass, ProvenanceKey, ProvenanceRole};

    #[test]
    fn application_wire_has_stable_compact_json_and_round_trips() {
        let term = WireTerm::Application {
            head_class: DescriptorApplicationHeadClass::BareReference,
            reference: WireApplicationReference {
                key: ProvenanceKey::new(ProvenanceRole::RuleLeftReference, 2),
                target: super::TargetSlot(3),
                authored_path: "Op::Gt".to_owned(),
            },
            path_key: ProvenanceKey::new(ProvenanceRole::RuleLeftPath, 4),
            arguments: vec![],
        };
        let json = serde_json::to_string(&term).unwrap();
        assert_eq!(
            json,
            r#"{"term_kind":"application","head_class":"bare_reference","reference":{"key":{"role":"rule_left_reference","ordinal":2},"target":3,"authored_path":"Op::Gt"},"path_key":{"role":"rule_left_path","ordinal":4},"arguments":[]}"#
        );
        let decoded: WireTerm = crate::json::from_slice(json.as_bytes()).unwrap();
        assert_eq!(serde_json::to_string(&decoded).unwrap(), json);
    }

    fn key() -> ProvenanceKey {
        ProvenanceKey::new(ProvenanceRole::RuleType, 0)
    }

    fn sort() -> super::WireSortReference {
        super::WireSortReference {
            key: key(),
            target: super::WireTypeReference {
                slot: super::TypeSlot(0),
                authored_path: "Value".to_owned(),
            },
        }
    }

    fn term() -> WireTerm {
        WireTerm::Anonymous {
            key: key(),
            sort: sort(),
            spelling: "_".to_owned(),
        }
    }

    #[test]
    fn static_constructor_traversal_maps_fields_and_propagates_errors() {
        let field = super::WireConstructorFieldDescriptor {
            name: "value".to_owned(),
            sort: super::WireTypeReference {
                slot: super::TypeSlot(1),
                authored_path: "Int".to_owned(),
            },
        };
        let mut map = crate::stage::tests::CountingMap::default();
        let mapped = field.clone().try_map_refs(&mut map).unwrap();
        assert_eq!(
            serde_json::to_value(&mapped).unwrap(),
            serde_json::to_value(&field).unwrap()
        );
        assert_eq!(map.calls, ["nominal"]);
        let constructor = super::WireConstructorDescriptor {
            sort: sort(),
            fields: vec![field],
        };
        let mut map = crate::stage::tests::CountingMap::default();
        let mapped = constructor.clone().try_map_refs(&mut map).unwrap();
        assert_eq!(
            serde_json::to_value(&mapped).unwrap(),
            serde_json::to_value(&constructor).unwrap()
        );
        assert_eq!(map.calls, ["sort", "nominal"]);
        for failure in ["sort", "nominal"] {
            let mut map = crate::stage::tests::CountingMap {
                fail: Some(failure),
                ..Default::default()
            };
            assert_eq!(
                constructor.clone().try_map_refs(&mut map).unwrap_err(),
                failure
            );
        }
    }

    fn assert_traversal<T: Clone + std::fmt::Debug + serde::Serialize>(
        value: T,
        reference: &'static str,
        count: usize,
        mut traverse: impl FnMut(T, &mut crate::stage::tests::CountingMap) -> Result<T, &'static str>,
    ) {
        let expected = serde_json::to_vec(&value).unwrap();
        let mut map = crate::stage::tests::CountingMap::default();
        let mapped = traverse(value.clone(), &mut map).unwrap();
        assert_eq!(serde_json::to_vec(&mapped).unwrap(), expected);
        assert_eq!(map.calls, vec![reference; count]);
        let mut map = crate::stage::tests::CountingMap {
            fail: Some(reference),
            ..Default::default()
        };
        assert_eq!(traverse(value, &mut map).unwrap_err(), reference);
        assert_eq!(map.calls, [reference]);
    }

    #[test]
    fn rule_and_constructor_traversals_preserve_data_and_propagate_errors() {
        assert_traversal(
            super::WireConstructorDescriptor {
                sort: sort(),
                fields: vec![],
            },
            "sort",
            1,
            super::WireConstructorDescriptor::try_map_refs,
        );
        assert_traversal(
            super::WireGrammarDescriptor::Subsort {
                key: key(),
                subsort: sort(),
                supersort: sort(),
            },
            "sort",
            2,
            super::WireGrammarDescriptor::try_map_refs,
        );
        assert_traversal(
            super::WireStructuredRule {
                sentence_kind: crate::SentenceKind::Transition,
                label: None,
                requires: None,
                priority: None,
                simplification: None,
                pattern_key: key(),
                result_key: key(),
                subject_sort: sort(),
                result_sort: sort(),
                bindings: vec![],
                subject: term(),
                result: term(),
            },
            "sort",
            4,
            super::WireStructuredRule::try_map_refs,
        );
        assert_traversal(
            super::WireHeadRule {
                sentence_kind: crate::SentenceKind::Transition,
                label: None,
                priority: None,
                pattern_key: key(),
                result_key: key(),
                head_sort: Some(sort()),
                configuration: None,
                computation_cell_name: None,
                bindings: vec![],
                subject: term(),
                result: super::WireHeadRuleResult::Replace(term()),
                requires: None,
                extras: vec![],
            },
            "sort",
            3,
            super::WireHeadRule::try_map_refs,
        );
    }
    fn configuration() -> super::WireConfigurationReference {
        super::WireConfigurationReference {
            key: key(),
            configuration: nominal(),
        }
    }

    fn nominal() -> super::WireTypeReference {
        super::WireTypeReference {
            slot: super::TypeSlot(0),
            authored_path: "Value".to_owned(),
        }
    }

    fn cells() -> super::WireRuleCells {
        crate::ProtocolRuleCells {
            key: key(),
            cells: vec![],
            remainder: crate::ProtocolRuleFrame::Exact,
        }
    }

    #[test]
    fn declaration_traversals_preserve_data_and_propagate_errors() {
        let declaration = super::WireCellDeclaration {
            key: key(),
            fields: vec![],
        };
        assert_traversal(
            super::WireSortDescriptor {
                parents: vec![nominal()],
            },
            "parent",
            1,
            super::WireSortDescriptor::try_map_refs,
        );
        assert_traversal(
            super::WireFixedConfiguration {
                root: crate::DescriptorConfigurationRoot::GeneratedTop,
                declaration: declaration.clone(),
                initializer: super::WireConfigurationInitializer {
                    key: key(),
                    owner_key: key(),
                    owner: nominal(),
                    body_key: key(),
                    variables: vec![],
                    cells: vec![],
                },
            },
            "initializer_owner",
            1,
            super::WireFixedConfiguration::try_map_refs,
        );
        assert_traversal(
            super::WireConfigurationRule {
                sentence_kind: crate::SentenceKind::Transition,
                label: None,
                priority: None,
                requires: None,
                claim: None,
                pattern_key: key(),
                result_key: key(),
                subject_configuration: configuration(),
                result_configuration: configuration(),
                bindings: vec![],
                subject: cells(),
                result: cells(),
            },
            "configuration",
            2,
            super::WireConfigurationRule::try_map_refs,
        );
        assert_traversal(
            super::WireContextAlias {
                declaration_key: key(),
                name_key: key(),
                name: "context".to_owned(),
                here_key: key(),
                here: "here".to_owned(),
                pattern_key: key(),
                configuration: configuration(),
                bindings: vec![],
                pattern: cells(),
            },
            "configuration",
            1,
            super::WireContextAlias::try_map_refs,
        );
        let expected = serde_json::to_vec(&declaration).unwrap();
        let mut map = crate::stage::tests::CountingMap::default();
        let mapped = crate::transport::configuration::map_declaration::<crate::WireStage, _, _>(
            declaration,
            &mut map,
        )
        .unwrap();
        assert_eq!(serde_json::to_vec(&mapped).unwrap(), expected);
        assert!(map.calls.is_empty());
    }
}
