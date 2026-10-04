//! Refined contract constructors and unchanged wire shapes.

use krs_ir::{
    Arguments, ArgumentsError, AtLeastTwo, AtLeastTwoError, BuiltinSort, DefinitionRuleBody,
    DefinitionSortRef, DefinitionTerm, DescriptorLiteral, DescriptorStage, DescriptorTerm,
    DescriptorTermArgument, IrRewrite, ItemKind, LabelId, LabelIdentity, ProductionFieldId,
    ProvenanceKey, ProvenanceRole, RuleSentence, SemanticRule, SemanticRuleBody, SemanticSortRef,
    SemanticTerm, SemanticValidationError, SentenceKind, testing,
};

fn literal() -> DescriptorTerm {
    DescriptorTerm::Literal {
        key: ProvenanceKey::new(ProvenanceRole::RuleLeftLiteral, 0),
        literal: DescriptorLiteral::Bool(true),
    }
}

#[test]
fn argument_adapter_rejects_both_mixed_orders_and_keeps_valid_json() {
    let positional = DescriptorTermArgument::Positional {
        value: Box::new(literal()),
    };
    let named = DescriptorTermArgument::Named {
        key: ProvenanceKey::new(ProvenanceRole::RuleLeftRecordFieldName, 0),
        field: ProductionFieldId::new("field").unwrap(),
        value: Box::new(literal()),
    };
    let expected = ArgumentsError::MixedForms;
    assert_eq!(
        expected.to_string(),
        "positional and named arguments are mixed"
    );
    for values in [
        vec![positional.clone(), named.clone()],
        vec![named.clone(), positional.clone()],
    ] {
        assert_eq!(
            Arguments::<DescriptorStage>::try_from(values.clone()).unwrap_err(),
            expected
        );
        let json = serde_json::to_string(&values).unwrap();
        assert!(
            serde_json::from_str::<Arguments<DescriptorStage>>(&json)
                .unwrap_err()
                .to_string()
                .contains(&expected.to_string())
        );
    }
    for values in [vec![], vec![positional], vec![named]] {
        let arguments = Arguments::<DescriptorStage>::try_from(values.clone()).unwrap();
        assert_eq!(
            serde_json::to_string(&arguments).unwrap(),
            serde_json::to_string(&values).unwrap()
        );
        assert_eq!(
            serde_json::from_value::<Arguments<DescriptorStage>>(
                serde_json::to_value(values).unwrap()
            )
            .unwrap(),
            arguments
        );
    }
}

#[test]
fn application_boundary_reports_context_free_mixed_forms() {
    let expected = ArgumentsError::MixedForms;
    let positional = serde_json::json!({"argument_kind": "positional", "value": literal()});
    let named = serde_json::json!({
        "argument_kind": "named",
        "key": ProvenanceKey::new(ProvenanceRole::RuleLeftRecordFieldName, 0),
        "field": "field", "value": literal(),
    });
    let key = ProvenanceKey::new(ProvenanceRole::RuleLeftPath, 0);
    for arguments in [
        vec![positional.clone(), named.clone()],
        vec![named, positional],
    ] {
        let json = serde_json::json!({
            "term_kind": "application", "head_class": "applied", "path_key": key,
            "reference": {
                "key": key,
                "application": {"application_source": "builtin", "application": "int_add"},
            },
            "arguments": arguments,
        });
        assert!(
            serde_json::from_value::<DescriptorTerm>(json)
                .unwrap_err()
                .to_string()
                .starts_with(&expected.to_string())
        );
    }
}

#[test]
fn named_arguments_are_nonempty_and_every_form_round_trips() {
    let named = || krs_ir::NamedTermArgument {
        key: ProvenanceKey::new(ProvenanceRole::RuleLeftRecordFieldName, 0),
        field: ProductionFieldId::new("field").unwrap(),
        value: Box::new(literal()),
    };
    let empty = Arguments::<DescriptorStage>::named(Vec::new());
    assert_eq!(empty, Arguments::default());
    assert!(!empty.is_named());
    for arguments in [
        empty,
        Arguments::Positional(vec![Box::new(literal())]),
        Arguments::Named(krs_ir::NonEmpty::new(named(), Vec::new())),
        Arguments::named(vec![named(), named()]),
    ] {
        if let Arguments::Named(values) = &arguments {
            assert!(!values.is_empty());
        }
        let json = serde_json::to_value(&arguments).unwrap();
        assert!(json.is_array());
        assert_eq!(
            serde_json::from_value::<Arguments<DescriptorStage>>(json).unwrap(),
            arguments
        );
    }
}

#[test]
fn disjunction_adapter_rejects_zero_and_one_operand_and_keeps_array_shape() {
    let expected = "or_bool requires at least two operands";
    for values in [vec![], vec![literal()]] {
        assert_eq!(
            AtLeastTwo::try_from(values.clone()).unwrap_err(),
            AtLeastTwoError
        );
        let json = serde_json::to_string(&values).unwrap();
        assert!(
            serde_json::from_str::<AtLeastTwo<DescriptorTerm>>(&json)
                .unwrap_err()
                .to_string()
                .contains(&AtLeastTwoError.to_string())
        );
        let json = serde_json::json!({
            "term_kind": "or_bool",
            "key": ProvenanceKey::new(ProvenanceRole::RuleLeftLiteral, 0),
            "arguments": values,
        });
        assert!(
            serde_json::from_value::<DescriptorTerm>(json)
                .unwrap_err()
                .to_string()
                .contains(expected)
        );
    }
    for values in [
        vec![literal(), literal()],
        vec![literal(), literal(), literal()],
    ] {
        let arguments = AtLeastTwo::try_from(values.clone()).unwrap();
        assert_eq!(
            serde_json::to_string(&arguments).unwrap(),
            serde_json::to_string(&values).unwrap()
        );
        assert_eq!(arguments.iter().count(), values.len());
    }
}

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
    let expected = krs_ir::DefinitionValidationError::RuleBodyNotRewrite(label.id().clone());
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

#[test]
fn precedence_chain_rejects_short_groups_and_keeps_array_shape() {
    use krs_ir::transport::detail::{GrammarProductionReason, TransportField};
    use krs_ir::{
        DescriptorGroupReference, DescriptorPrecedenceChain, GrammarTransportError,
        ProductionGroupId,
    };
    let key = ProvenanceKey::new(ProvenanceRole::PrecedenceChain, 0);
    let group = |name: &str, ordinal| DescriptorGroupReference {
        key: ProvenanceKey::new(ProvenanceRole::PrecedenceGroupReference, ordinal),
        group: ProductionGroupId::new(name).unwrap(),
    };
    for (groups, expected) in [
        (
            vec![],
            GrammarTransportError::EmptyCollection(TransportField::PrecedenceGroups),
        ),
        (
            vec![group("one", 0)],
            GrammarTransportError::InvalidProduction(GrammarProductionReason::ShortPrecedenceChain),
        ),
    ] {
        assert_eq!(
            DescriptorPrecedenceChain::new(key.clone(), groups.clone()).unwrap_err(),
            expected
        );
        let json = serde_json::json!({"key": key, "groups": groups});
        assert!(
            serde_json::from_value::<DescriptorPrecedenceChain>(json)
                .unwrap_err()
                .to_string()
                .contains(&expected.to_string())
        );
    }
    let groups = vec![group("one", 0), group("two", 1), group("three", 2)];
    let chain = DescriptorPrecedenceChain::new(key.clone(), groups.clone()).unwrap();
    assert_eq!(
        serde_json::to_value(chain).unwrap(),
        serde_json::json!({"key": key, "groups": groups})
    );
}
