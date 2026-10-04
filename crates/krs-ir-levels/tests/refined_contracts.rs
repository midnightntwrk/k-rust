//! Refined Semantic and Definition IR rule bodies and their unchanged wire shapes.

use krs_ir::{BuiltinSort, ItemKind, SentenceKind, testing};
use krs_ir_levels::{
    DefinitionRuleBody, DefinitionSortRef, DefinitionTerm, DefinitionValidationError, IrRewrite,
    LabelId, LabelIdentity, RuleSentence, SemanticRule, SemanticRuleBody, SemanticSortRef,
    SemanticTerm, SemanticValidationError,
};

#[test]
fn semantic_rule_body_rejects_nonrewrites_with_the_rule_identity() {
    let id = testing::item_in(testing::smoke_package(), "rules", "rule", ItemKind::Rule);
    let term = SemanticTerm::token(testing::origin("token"), SemanticSortRef::int(), "1").unwrap();
    let expected = SemanticValidationError::RuleBodyNotRewrite(Box::new(id.clone()));
    assert_eq!(
        SemanticRule::new(
            testing::origin("rule"),
            id.clone(),
            SentenceKind::Transition,
            vec![],
            term.clone()
        )
        .unwrap_err(),
        expected
    );
    let rewrite = IrRewrite::new(
        testing::origin("rewrite"),
        SemanticSortRef::int(),
        term.clone(),
        term.clone(),
    );
    let rule = SemanticRule::new(
        testing::origin("rule"),
        id,
        SentenceKind::Transition,
        vec![],
        rewrite.clone().into(),
    )
    .unwrap();
    assert_eq!(
        serde_json::to_value(SemanticRuleBody::Term(rewrite.clone())).unwrap(),
        serde_json::to_value(SemanticTerm::from(rewrite.clone())).unwrap()
    );
    let mut json = serde_json::to_value(rule).unwrap();
    json["body"] = serde_json::to_value(term).unwrap();
    assert!(
        serde_json::from_value::<SemanticRule>(json)
            .unwrap_err()
            .to_string()
            .contains(&expected.to_string())
    );
}

#[test]
fn definition_rule_body_rejects_nonrewrites_with_the_label_identity() {
    let term = DefinitionTerm::token(
        testing::origin("token"),
        DefinitionSortRef::Builtin(BuiltinSort::Int),
        "1",
    )
    .unwrap();
    let label = LabelIdentity::new(LabelId::new("label").unwrap(), "rule-label").unwrap();
    let expected = DefinitionValidationError::RuleBodyNotRewrite(label.id().clone());
    assert_eq!(
        RuleSentence::new(
            testing::origin("rule"),
            label.clone(),
            SentenceKind::Transition,
            vec![],
            term.clone()
        )
        .unwrap_err(),
        expected
    );
    let rewrite = IrRewrite::new(
        testing::origin("rewrite"),
        DefinitionSortRef::Builtin(BuiltinSort::Int),
        term.clone(),
        term.clone(),
    );
    let rule = RuleSentence::new(
        testing::origin("rule"),
        label,
        SentenceKind::Transition,
        vec![],
        rewrite.clone().into(),
    )
    .unwrap();
    assert_eq!(
        serde_json::to_value(DefinitionRuleBody::Term(rewrite.clone())).unwrap(),
        serde_json::to_value(DefinitionTerm::from(rewrite.clone())).unwrap()
    );
    let mut json = serde_json::to_value(rule).unwrap();
    json["body"] = serde_json::to_value(term).unwrap();
    assert!(
        serde_json::from_value::<RuleSentence>(json)
            .unwrap_err()
            .to_string()
            .contains(&expected.to_string())
    );
}
