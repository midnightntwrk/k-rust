//! Indexed, unresolved host payloads emitted as static macro data.

use serde::{Deserialize, Serialize};

use crate::stage::{WireStage, stage_shape};
use crate::transport::grammar::{
    CellTermField, Production, ProductionAttribute, ProductionItem, ProductionOwner, RuleCondition,
    StageGrammarDescriptor, StructuredRule, Term, TermArgument,
};
use crate::transport::head_rule::HeadRule;
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

stage_shape! {
    /// The payload kinds supported by static indexed macro data.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(rename = "WirePayload", rename_all = "snake_case", deny_unknown_fields, bound(serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize, S::ContextAlias: Serialize, S::Configuration: Serialize, S::HeadRuleCell: Serialize", deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>, S::ContextAlias: Deserialize<'de>, S::Configuration: Deserialize<'de>, S::HeadRuleCell: Deserialize<'de>"))]
    pub enum StaticPayload<S: Stage> {
        /// Constructor declaration.
        Constructor(value: StaticConstructor<S> => [nested]),
        /// Object-grammar sentence.
        Grammar(value: Box<StageGrammarDescriptor<S>> => [box nested]),
        /// Structured relational sentence.
        StructuredRule(value: Box<StructuredRule<S>> => [box nested]),
        /// Authored computation-head rule.
        HeadRule(value: Box<HeadRule<S>> => [box nested]),
    }
}

/// Static wire-stage payload.
pub type WirePayload = StaticPayload<WireStage>;

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

    #[test]
    fn static_payload_traversal_covers_every_supported_kind() {
        let key = key();
        let payloads = [
            super::WirePayload::Constructor(super::WireConstructorDescriptor {
                sort: sort(),
                fields: vec![],
            }),
            super::WirePayload::Grammar(Box::new(super::WireGrammarDescriptor::Subsort {
                key: key.clone(),
                subsort: sort(),
                supersort: sort(),
            })),
            super::WirePayload::StructuredRule(Box::new(super::WireStructuredRule {
                sentence_kind: crate::SentenceKind::Transition,
                label: None,
                requires: None,
                priority: None,
                simplification: None,
                pattern_key: key.clone(),
                result_key: key.clone(),
                subject_sort: sort(),
                result_sort: sort(),
                bindings: vec![],
                subject: term(),
                result: term(),
            })),
            super::WirePayload::HeadRule(Box::new(super::WireHeadRule {
                sentence_kind: crate::SentenceKind::Transition,
                label: None,
                priority: None,
                pattern_key: key.clone(),
                result_key: key,
                head_sort: Some(sort()),
                configuration: None,
                computation_cell_name: None,
                bindings: vec![],
                subject: term(),
                result: super::WireHeadRuleResult::Replace(term()),
                requires: None,
                extras: vec![],
            })),
        ];
        for (payload, count) in payloads.into_iter().zip([1, 2, 4, 3]) {
            let expected = serde_json::to_vec(&payload).unwrap();
            let mut map = crate::stage::tests::CountingMap::default();
            let mapped = payload.clone().try_map_refs(&mut map).unwrap();
            assert_eq!(serde_json::to_vec(&mapped).unwrap(), expected);
            assert_eq!(map.calls, vec!["sort"; count]);
            let mut map = crate::stage::tests::CountingMap {
                fail: Some("sort"),
                ..Default::default()
            };
            assert_eq!(payload.try_map_refs(&mut map).unwrap_err(), "sort");
            assert_eq!(map.calls, ["sort"]);
        }
    }
}
