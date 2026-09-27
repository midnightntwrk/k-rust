//! Indexed, unresolved host rule payloads emitted as static macro data.

#![allow(missing_docs)]

use serde::{Deserialize, Serialize};

use crate::{
    BuiltinSort, DescriptorApplicationHeadClass, DescriptorLiteral, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSimplification, ProductionFieldId, ProtocolHeadRuleBinding,
    ProtocolHeadRuleExtra, ProtocolHeadRuleResult, ProvenanceKey, SentenceKind,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireTypeReference {
    pub slot: usize,
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
    pub target: usize,
    pub authored_path: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "argument_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum WireTermArgument {
    Positional {
        value: Box<WireTerm>,
    },
    Named {
        key: ProvenanceKey,
        field: ProductionFieldId,
        value: Box<WireTerm>,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireCellTermField {
    pub key: ProvenanceKey,
    pub field: ProductionFieldId,
    pub value: Box<WireTerm>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "term_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum WireTerm {
    Variable {
        key: ProvenanceKey,
        path_key: ProvenanceKey,
        name: String,
    },
    Application {
        head_class: DescriptorApplicationHeadClass,
        reference: WireApplicationReference,
        path_key: ProvenanceKey,
        arguments: Vec<WireTermArgument>,
    },
    Literal {
        key: ProvenanceKey,
        literal: DescriptorLiteral,
    },
    Wildcard {
        key: ProvenanceKey,
    },
    BuiltinToken {
        key: ProvenanceKey,
        sort: BuiltinSort,
        value: String,
    },
    Anonymous {
        key: ProvenanceKey,
        sort: WireSortReference,
        spelling: String,
    },
    OrBool {
        key: ProvenanceKey,
        arguments: Vec<WireTerm>,
    },
    Cell {
        key: ProvenanceKey,
        declaration: WireTypeReference,
        fields: Vec<WireCellTermField>,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireRuleCondition {
    pub key: ProvenanceKey,
    pub term: WireTerm,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireStructuredRule {
    pub sentence_kind: SentenceKind,
    pub label: Option<DescriptorRuleLabel>,
    pub requires: Option<WireRuleCondition>,
    pub priority: Option<DescriptorRulePriority>,
    pub simplification: Option<DescriptorSimplification>,
    pub pattern_key: ProvenanceKey,
    pub result_key: ProvenanceKey,
    pub subject_sort: WireSortReference,
    pub result_sort: WireSortReference,
    pub bindings: Vec<String>,
    pub subject: WireTerm,
    pub result: WireTerm,
}

pub type WireHeadRuleBinding = ProtocolHeadRuleBinding<WireSortReference>;
pub type WireHeadRuleResult = ProtocolHeadRuleResult<WireTerm>;
pub type WireHeadRuleExtra = ProtocolHeadRuleExtra<WireHeadRuleCellReference, WireTerm>;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireHeadRuleCellReference {
    pub key: ProvenanceKey,
    pub name: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireHeadRule {
    pub sentence_kind: SentenceKind,
    pub label: Option<DescriptorRuleLabel>,
    pub priority: Option<DescriptorRulePriority>,
    pub pattern_key: ProvenanceKey,
    pub result_key: ProvenanceKey,
    pub head_sort: Option<WireSortReference>,
    pub configuration: Option<WireConfigurationReference>,
    pub computation_cell_name: Option<String>,
    pub bindings: Vec<WireHeadRuleBinding>,
    pub subject: WireTerm,
    pub result: WireHeadRuleResult,
    pub requires: Option<WireRuleCondition>,
    pub extras: Vec<WireHeadRuleExtra>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub enum WirePayload {
    StructuredRule(Box<WireStructuredRule>),
    HeadRule(Box<WireHeadRule>),
}

#[cfg(test)]
mod tests {
    use super::{WireApplicationReference, WireTerm};
    use crate::{DescriptorApplicationHeadClass, ProvenanceKey};

    #[test]
    fn application_wire_has_stable_compact_json_and_round_trips() {
        let term = WireTerm::Application {
            head_class: DescriptorApplicationHeadClass::BareReference,
            reference: WireApplicationReference {
                key: ProvenanceKey::new("rule_left_reference", 2).unwrap(),
                target: 3,
                authored_path: "Op::Gt".to_owned(),
            },
            path_key: ProvenanceKey::new("rule_left_path", 4).unwrap(),
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
}
