use std::sync::Arc;

use std::collections::BTreeMap;

use k_rust::definition::{
    Attributes, ClaimId, Definition, FlatImport, FlatModule, HeadShape, ProductionItem,
    ResolvedDefinition, RuleHead, RuleId, Sentence, match_rule_label,
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

/// An alias `P #as V` matches the terms `P` matches, so the rule it heads is headed by `P`'s
/// symbol, in every position the head is read from.
#[test]
fn matches_the_label_under_an_alias() {
    let alias = |pattern: Term| Term::As {
        pattern: Box::new(pattern),
        alias: Box::new(Term::variable("V")),
    };
    let aliased_rewrite = rule(
        Term::Rewrite {
            left: Box::new(alias(alias(apply(Label::new("aliased"))))),
            right: Box::new(Term::variable("RESULT")),
        },
        Attributes::default(),
    );
    let aliased_direct = rule(alias(apply(Label::new("direct"))), Attributes::default());
    let with_config = rule(
        Term::Apply {
            label: Label::new("#withConfig"),
            arguments: vec![
                Term::Rewrite {
                    left: Box::new(alias(apply(Label::new("configuredRewrite")))),
                    right: Box::new(Term::variable("RESULT")),
                },
                Term::variable("CONFIG"),
            ],
        },
        Attributes::default(),
    );

    assert_eq!(match_rule_label(&aliased_rewrite), Label::new("aliased"));
    assert_eq!(match_rule_label(&aliased_direct), Label::new("direct"));
    assert_eq!(
        match_rule_label(&with_config),
        Label::new("configuredRewrite")
    );
    let catalog = k_rust::definition::RuleCatalog::from_visible([&aliased_rewrite]);
    assert_eq!(catalog.rules_for(&Label::new("aliased")), [RuleId(0)]);
}

/// Every shape of rule body, built from one head `f(X)` by the wrappers the readers of a rule's
/// head have disagreed on (root aliases, nested or not; a top rewrite or none; `#withConfig`;
/// an injection around the head), is read by [`RuleHead::of`] as headed by the same symbol,
/// with the shape, context and injected argument the wrappers state. An alias names the matched
/// term and constrains nothing, so wrapping the left side in any number of aliases never changes
/// the head; `inj` is a symbol of its own and is reported as the head, its argument separately.
#[test]
fn the_rule_head_is_read_through_every_wrapper() {
    let head = || Term::Apply {
        label: Label::new("f"),
        arguments: vec![Term::variable("X")],
    };
    let alias = |pattern: Term, name: &str| Term::As {
        pattern: Box::new(pattern),
        alias: Box::new(Term::variable(name)),
    };
    let inj = |argument: Term| Term::Apply {
        label: Label::new("inj"),
        arguments: vec![argument],
    };
    let with_config = |rule: Term| Term::Apply {
        label: Label::new("#withConfig"),
        arguments: vec![rule, Term::variable("CONFIG")],
    };
    let aliased = |term: Term, aliases: usize| {
        (0..aliases).fold(term, |term, index| alias(term, &format!("V{index}")))
    };
    for aliases in 0..3 {
        for injected in [false, true] {
            for rewrite_at_top in [false, true] {
                for configured in [false, true] {
                    let left = if injected {
                        aliased(inj(aliased(head(), aliases)), aliases)
                    } else {
                        aliased(head(), aliases)
                    };
                    let mut body = if rewrite_at_top { rewrite(left) } else { left };
                    if configured {
                        body = with_config(body);
                    }
                    let case = format!("{body}");
                    let read = RuleHead::of(&body);
                    let expected = if injected { "inj" } else { "f" };
                    assert_eq!(
                        read.label().map(|l| l.name.as_str()),
                        Some(expected),
                        "{case}"
                    );
                    assert_eq!(
                        read.injected().map(|l| l.name.as_str()),
                        injected.then_some("f"),
                        "{case}"
                    );
                    assert_eq!(
                        read.shape(),
                        if rewrite_at_top {
                            HeadShape::TopRewrite
                        } else {
                            HeadShape::NoRewrite
                        },
                        "{case}"
                    );
                    assert_eq!(read.context.is_some(), configured, "{case}");
                    assert_eq!(
                        match_rule_label(&rule(body.clone(), Attributes::default())).name,
                        expected,
                        "{case}"
                    );
                }
            }
        }
    }
    // A body whose root is not an application has no head.
    assert!(
        RuleHead::of(&rewrite(Term::variable("X")))
            .label()
            .is_none()
    );
    // `#withConfig` around a body without an application head is read as written.
    let opaque = with_config(rewrite(Term::variable("X")));
    assert_eq!(
        RuleHead::of(&opaque).label().map(|l| l.name.as_str()),
        Some("#withConfig")
    );
}

#[test]
fn derives_visible_local_sorted_and_grouped_sentence_views() {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            Arc::new(rule(apply(Label::new("base")), Attributes::default())),
            Arc::new(claim(apply(Label::new("baseClaim")))),
            Arc::new(Sentence::Context {
                body: apply(Label::new("baseContext")),
                requires: truth(),
                attributes: Attributes::default(),
            }),
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
            Arc::new(rule(apply(Label::new("local")), Attributes::default())),
            Arc::new(rule(truth(), Attributes::default())),
            Arc::new(claim(apply(Label::new("localClaim")))),
            Arc::new(Sentence::Context {
                body: apply(Label::new("localContext")),
                requires: truth(),
                attributes: Attributes::default(),
            }),
            Arc::new(Sentence::ContextAlias {
                body: apply(Label::new("aliasContext")),
                requires: truth(),
                attributes: Attributes::default(),
            }),
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
        &[k_rust::definition::LabelHead::new("ruleMacro")]
            .into_iter()
            .collect()
    );
    assert_eq!(
        rules.all_macro_labels(&productions),
        [
            k_rust::definition::LabelHead::new("productionMacro"),
            k_rust::definition::LabelHead::new("ruleMacro"),
        ]
        .into_iter()
        .collect()
    );
    assert!(
        rules
            .rules()
            .any(|(_, rule)| match_rule_label(rule).name == "productionMacro")
    );
}
