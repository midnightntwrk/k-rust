//! Indexed, unresolved host payloads emitted as static macro data.

#![allow(missing_docs)]

use serde::{Deserialize, Serialize};

use crate::{
    BuiltinSort, DescriptorApplicationHeadClass, DescriptorAssociativitySentence,
    DescriptorFieldReference, DescriptorFormatFragment, DescriptorGroupReference,
    DescriptorLexicalPrecedence, DescriptorLiteral, DescriptorPrecedenceChain, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSimplification, HookOperation, ProductionFieldId,
    ProtocolHeadRuleBinding, ProtocolHeadRuleExtra, ProtocolHeadRuleResult, ProvenanceKey,
    SentenceKind, StrictnessKind,
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

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireConstructorFieldDescriptor {
    pub name: String,
    pub sort: WireTypeReference,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireConstructorDescriptor {
    pub sort: WireSortReference,
    pub syntax: Option<String>,
    pub fields: Vec<WireConstructorFieldDescriptor>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireContextAliasReference {
    pub key: ProvenanceKey,
    pub slot: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "item_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum WireProductionItem {
    Terminal {
        key: ProvenanceKey,
        text: String,
    },
    NonTerminal {
        key: ProvenanceKey,
        field_key: ProvenanceKey,
        declaration_key: Option<ProvenanceKey>,
        field: ProductionFieldId,
        sort: Box<WireSortReference>,
    },
    RegexTerminal {
        key: ProvenanceKey,
        precede_regex: Option<String>,
        regex: String,
        follow_regex: Option<String>,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "attribute_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum WireProductionAttribute {
    Documentation {
        key: ProvenanceKey,
        text: String,
    },
    Function {
        key: ProvenanceKey,
    },
    Total {
        key: ProvenanceKey,
    },
    Hook {
        key: ProvenanceKey,
        operation: HookOperation,
    },
    Alias {
        key: ProvenanceKey,
    },
    Token {
        key: ProvenanceKey,
        lexical_precedence: Option<DescriptorLexicalPrecedence>,
    },
    Group {
        reference: DescriptorGroupReference,
    },
    Bracket {
        key: ProvenanceKey,
    },
    Avoid {
        key: ProvenanceKey,
    },
    Format {
        key: ProvenanceKey,
        fragments: Vec<DescriptorFormatFragment>,
    },
    Strictness {
        key: ProvenanceKey,
        kind: StrictnessKind,
        using: Option<WireContextAliasReference>,
        fields: Vec<DescriptorFieldReference>,
        result_sort: Box<WireSortReference>,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(
    tag = "production_owner",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum WireProductionOwner {
    Constructor {
        constructor: WireApplicationReference,
    },
    TokenSort {
        sort: WireSortReference,
    },
    BracketSort {
        sort: WireSortReference,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WireProduction {
    pub key: ProvenanceKey,
    pub template_key: Option<ProvenanceKey>,
    pub owner: WireProductionOwner,
    pub result_sort: WireSortReference,
    pub items: Vec<WireProductionItem>,
    pub attributes: Vec<WireProductionAttribute>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(
    tag = "grammar_kind",
    content = "grammar",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum WireGrammarDescriptor {
    Production(WireProduction),
    Subsort {
        key: ProvenanceKey,
        subsort: WireSortReference,
        supersort: WireSortReference,
    },
    Precedence {
        key: ProvenanceKey,
        chains: Vec<DescriptorPrecedenceChain>,
    },
    Associativity {
        key: ProvenanceKey,
        sentences: Vec<DescriptorAssociativitySentence>,
    },
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
    Constructor(WireConstructorDescriptor),
    Grammar(Box<WireGrammarDescriptor>),
    StructuredRule(Box<WireStructuredRule>),
    HeadRule(Box<WireHeadRule>),
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
                target: 3,
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
}
