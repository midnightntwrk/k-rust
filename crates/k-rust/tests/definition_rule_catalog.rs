use std::collections::BTreeMap;

use k_rust::definition::{
    Attributes, ClaimId, Definition, FlatImport, FlatModule, ProductionItem, ResolvedDefinition,
    RuleId, Sentence, match_rule_label,
};
use k_rust::kast::{Label, Sort, Term};
use serde_json::Value;

fn attrs(keys: &[&str]) -> Attributes {
    Attributes::new(
        keys.iter()
            .map(|key| ((*key).into(), Value::String(String::new())))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn rule(body: Term, attributes: Attributes) -> Sentence {
    Sentence::Rule {
        body,
        requires: truth(),
        ensures: truth(),
        attributes,
    }
}

fn claim(body: Term) -> Sentence {
    Sentence::Claim {
        body,
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    }
}

fn apply(label: Label) -> Term {
    Term::Apply {
        label,
        arguments: Vec::new(),
    }
}

fn rewrite(left: Term) -> Term {
    Term::Rewrite {
        left: Box::new(left),
        right: Box::new(Term::variable("RESULT")),
    }
}

#[test]
fn matches_direct_rewrite_and_with_config_labels() {
    let parameterized = Label::with_parameters("direct", vec![Sort::new("Int")]);
    let direct = rule(apply(parameterized.clone()), Attributes::default());
    let rewritten = rule(rewrite(apply(Label::new("rewrite"))), Attributes::default());
    let with_config = rule(
        Term::Apply {
            label: Label::new("#withConfig"),
            arguments: vec![apply(Label::new("configured")), Term::variable("CONFIG")],
        },
        Attributes::default(),
    );
    let with_config_rewrite = rule(
        Term::Apply {
            label: Label::new("#withConfig"),
            arguments: vec![rewrite(apply(Label::new("configuredRewrite")))],
        },
        Attributes::default(),
    );
    let unmatched = rule(truth(), Attributes::default());

    assert_eq!(match_rule_label(&direct), parameterized);
    assert_eq!(match_rule_label(&rewritten), Label::new("rewrite"));
    assert_eq!(match_rule_label(&with_config), Label::new("configured"));
    assert_eq!(
        match_rule_label(&with_config_rewrite),
        Label::new("configuredRewrite")
    );
    assert_eq!(match_rule_label(&unmatched), Label::new(""));
}

#[test]
fn derives_visible_local_sorted_and_grouped_sentence_views() {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            rule(apply(Label::new("base")), Attributes::default()),
            claim(apply(Label::new("baseClaim"))),
            Sentence::Context {
                body: apply(Label::new("baseContext")),
                requires: truth(),
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    };
    let main = FlatModule {
        name: "MAIN".into(),
        imports: vec![FlatImport {
            name: "BASE".into(),
            public: true,
        }],
        local_sentences: vec![
            rule(apply(Label::new("local")), Attributes::default()),
            rule(truth(), Attributes::default()),
            claim(apply(Label::new("localClaim"))),
            Sentence::Context {
                body: apply(Label::new("localContext")),
                requires: truth(),
                attributes: Attributes::default(),
            },
            Sentence::ContextAlias {
                body: apply(Label::new("aliasContext")),
                requires: truth(),
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    };
    let resolved = ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![main, base],
        attributes: Attributes::default(),
    })
    .unwrap();
    let catalog = resolved.rule_catalog(resolved.main_module_id());

    assert_eq!(catalog.rules().count(), 3);
    assert_eq!(
        catalog.local_rule_ids(),
        &[RuleId(1), RuleId(2)].into_iter().collect()
    );
    assert_eq!(catalog.local_rules().count(), 2);
    assert_eq!(catalog.sorted_rules().count(), 3);
    assert_eq!(catalog.rules_for(&Label::new("base")), [RuleId(0)]);
    assert_eq!(catalog.rules_for(&Label::new("local")), [RuleId(1)]);
    assert_eq!(catalog.rules_for(&Label::new("")), [RuleId(2)]);
    assert_eq!(catalog.claims().count(), 2);
    assert_eq!(
        catalog.local_claim_ids(),
        &[ClaimId(1)].into_iter().collect()
    );
    assert_eq!(catalog.local_claims().count(), 1);
    assert_eq!(catalog.contexts().count(), 2);
}

#[test]
fn combines_rule_and_production_macro_labels() {
    let macro_production = Sentence::Production {
        label: Some(Label::new("productionMacro")),
        parameters: Vec::new(),
        sort: Sort::new("K"),
        items: vec![ProductionItem::Terminal("macro".into())],
        attributes: attrs(&["macro"]),
    };
    let macro_rule = rule(apply(Label::new("ruleMacro")), attrs(&["alias-rec"]));
    let production_lhs_rule = rule(
        rewrite(apply(Label::new("productionMacro"))),
        Attributes::default(),
    );
    let sentences = [&macro_production, &macro_rule, &production_lhs_rule];
    let productions = k_rust::definition::ProductionCatalog::from_visible(sentences);
    let rules = k_rust::definition::RuleCatalog::from_visible(sentences);

    assert_eq!(
        rules.macro_labels(),
        &[Label::new("ruleMacro")].into_iter().collect()
    );
    assert_eq!(
        rules.all_macro_labels(&productions),
        [Label::new("productionMacro"), Label::new("ruleMacro")]
            .into_iter()
            .collect()
    );
    let production_lhs = rules
        .rules()
        .find_map(|(id, rule)| (match_rule_label(rule).name == "productionMacro").then_some(id))
        .unwrap();
    assert!(rules.rule_lhs_has_macro_label(production_lhs, &productions));
}
