use std::collections::{BTreeMap, BTreeSet};

use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, LOCATION_ATTRIBUTE,
    PartialOrder, ProductionItem, SOURCE_ATTRIBUTE, Sentence, StructuralCheckBackend,
    StructuralCheckOptions, check_anonymous_variables, check_associativity, check_duplicate_labels,
    check_k_terms, check_module, check_module_with_options, check_rewrites, check_rhs_variables,
    check_sort_top_uniqueness, check_syntax_groups, check_tokens, compute_priorities,
};
use k_rust::diagnostic::{DiagnosticCode, Severity};
use k_rust::kast::{Label, Sort, Term};
use serde_json::{Value, json};

fn attrs(entries: &[(&str, Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn token(value: &str) -> Term {
    Term::Token {
        token: value.into(),
        sort: Sort::new("Int"),
    }
}

fn rewrite(left: Term, right: Term) -> Term {
    Term::Rewrite {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn as_pattern(pattern: Term, alias: Term) -> Term {
    Term::As {
        pattern: Box::new(pattern),
        alias: Box::new(alias),
    }
}

fn located() -> Attributes {
    attrs(&[
        (SOURCE_ATTRIBUTE, json!("checks.k")),
        (LOCATION_ATTRIBUTE, json!([1, 1, 1, 20])),
    ])
}

fn rule(attributes: Attributes) -> Sentence {
    Sentence::Rule {
        body: truth(),
        requires: truth(),
        ensures: truth(),
        attributes,
    }
}

fn production(
    label: Option<&str>,
    sort: &str,
    arguments: &[&str],
    attributes: Attributes,
) -> Sentence {
    Sentence::Production {
        label: label.map(Label::new),
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: arguments
            .iter()
            .map(|argument| ProductionItem::NonTerminal {
                sort: Sort::new(*argument),
                name: None,
            })
            .collect(),
        attributes,
    }
}

#[test]
fn duplicate_labels_ignore_context_aliases_and_preserve_location() {
    let located = attrs(&[
        ("label", json!("same")),
        (SOURCE_ATTRIBUTE, json!("definition.k")),
        (LOCATION_ATTRIBUTE, json!([3, 4, 3, 12])),
    ]);
    let first = rule(attrs(&[("label", json!("same"))]));
    let second = rule(located);
    let alias = Sentence::ContextAlias {
        body: truth(),
        requires: truth(),
        attributes: attrs(&[("label", json!("same"))]),
    };
    let diagnostics = check_duplicate_labels(&[&first, &second, &alias]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::DuplicateSentenceLabel);
    assert_eq!(diagnostics[0].severity, Severity::Error);
    assert_eq!(diagnostics[0].source.as_deref(), Some("definition.k"));
    assert_eq!(diagnostics[0].location.unwrap().start_column, 4);
}

#[test]
fn syntax_groups_warn_when_tags_have_different_priorities() {
    let priority = Sentence::SyntaxPriority {
        priorities: vec![vec!["high".into()], vec!["low".into()]],
        attributes: Attributes::default(),
    };
    let group = Sentence::SyntaxAssociativity {
        associativity: Associativity::Left,
        tags: vec!["low".into(), "unrelated".into(), "high".into()],
        attributes: Attributes::default(),
    };
    let priorities = compute_priorities([&priority]).unwrap();
    let diagnostics = check_syntax_groups(&[&group], &priorities);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].severity, Severity::Warning);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidAssociativity);
    assert_eq!(
        diagnostics[0].message,
        "Symbols high and low are in the same associativity group, but have different priorities."
    );
}

#[test]
fn associativity_attributes_require_the_java_subsort_conditions() {
    let invalid = production(
        Some("op"),
        "Expr",
        &["Left", "Right"],
        attrs(&[
            ("left", json!("")),
            ("right", json!("")),
            ("non-assoc", json!("")),
        ]),
    );
    let unary = production(
        Some("unary"),
        "Expr",
        &["Other"],
        attrs(&[("left", json!(""))]),
    );
    let subsorts = PartialOrder::new([(Sort::new("Unused"), Sort::new("Top"))]).unwrap();
    let diagnostics = check_associativity(&[&invalid, &unary], &subsorts);

    assert_eq!(diagnostics.len(), 3);
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code == DiagnosticCode::InvalidAssociativity)
    );
    assert!(diagnostics[0].message.contains("attribute not permitted"));
    assert!(diagnostics[0].message.contains("Hint:"));
}

#[test]
fn detects_multiple_top_sorts_but_exempts_cell() {
    let sort_a = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("A"),
        attributes: Attributes::default(),
    };
    let cell = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Cell"),
        attributes: Attributes::default(),
    };
    let subsorts = PartialOrder::new([
        (Sort::new("A"), Sort::new("KList")),
        (Sort::new("A"), Sort::new("Bag")),
        (Sort::new("Cell"), Sort::new("KList")),
        (Sort::new("Cell"), Sort::new("Bag")),
    ])
    .unwrap();
    let diagnostics = check_sort_top_uniqueness(&[&sort_a, &cell], &subsorts);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::MultipleTopSorts);
    assert_eq!(
        diagnostics[0].message,
        "Multiple top sorts found for A: KList and Bag."
    );
}

#[test]
fn token_sort_productions_allow_only_java_exceptions() {
    let illegal = production(Some("ordinary"), "Int", &[], Attributes::default());
    let function = production(
        Some("function"),
        "Int",
        &[],
        attrs(&[("function", json!(""))]),
    );
    let macro_production = production(Some("macro"), "Int", &[], Attributes::default());
    let internal = production(Some("internal"), "#Internal", &[], Attributes::default());
    let token_sorts = [Sort::new("Int"), Sort::new("#Internal")]
        .into_iter()
        .collect();
    let macro_labels = [Label::new("macro")].into_iter().collect();
    let diagnostics = check_tokens(
        &[&illegal, &function, &macro_production, &internal],
        &token_sorts,
        &macro_labels,
    );

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidTokenProduction);
}

#[test]
fn module_runner_checks_local_sentences_against_visible_indexes() {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::new("Int"),
                attributes: attrs(&[("token", json!(""))]),
            },
            Sentence::SyntaxPriority {
                priorities: vec![vec!["high".into()], vec!["low".into()]],
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
            production(Some("ordinary"), "Int", &[], Attributes::default()),
            Sentence::SyntaxAssociativity {
                associativity: Associativity::Left,
                tags: vec!["high".into(), "low".into()],
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![main, base],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_module(&resolved, resolved.main_module_id()).unwrap();

    assert_eq!(diagnostics.len(), 2);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<BTreeSet<_>>(),
        [
            DiagnosticCode::InvalidAssociativity,
            DiagnosticCode::InvalidTokenProduction,
        ]
        .into_iter()
        .collect()
    );
}

#[test]
fn module_runner_includes_term_structure_checks() {
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![rule_with_body(token("0"))],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_module(&resolved, resolved.main_module_id()).unwrap();

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidRewrite);
    assert_eq!(
        diagnostics[0].message,
        "Rules must have at least one rewrite."
    );
}

#[test]
fn as_patterns_require_variable_or_semantic_cast_aliases() {
    let invalid = rule_with_body(as_pattern(token("0"), token("1")));
    let variable = rule_with_body(as_pattern(token("0"), Term::variable("X")));
    let cast = rule_with_body(as_pattern(
        token("0"),
        Term::apply("#SemanticCastToInt", vec![Term::variable("X")]),
    ));
    let diagnostics = check_k_terms(&[&invalid, &variable, &cast]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidAsPattern);
    assert_eq!(
        diagnostics[0].message,
        "Found #as pattern where the right side is not a variable."
    );
}

#[test]
fn rewrite_check_matches_nested_missing_as_and_existential_cases() {
    let nested = rule_with_body(rewrite(
        rewrite(token("1"), token("2")),
        rewrite(token("3"), token("4")),
    ));
    let missing = rule_with_body(token("0"));
    let as_on_rhs = rule_with_body(rewrite(
        token("0"),
        as_pattern(token("1"), Term::variable("X")),
    ));
    let rewrite_inside_as = rule_with_body(as_pattern(
        rewrite(token("0"), token("1")),
        Term::variable("X"),
    ));
    let existential_on_lhs = rule_with_body(rewrite(Term::variable("?X"), token("0")));
    let diagnostics = check_rewrites(&[
        &nested,
        &missing,
        &as_on_rhs,
        &rewrite_inside_as,
        &existential_on_lhs,
    ]);

    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.message == "Rewrites are not allowed to be nested.")
            .count(),
        2
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message == "Rules must have at least one rewrite." })
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message == "#as is not allowed in the RHS of a rule." })
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Rewrites are not allowed inside an #as pattern."
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::InvalidExistentialVariable
            && diagnostic
                .message
                .starts_with("Existential variable ?X found in LHS")
    }));
}

#[test]
fn claims_need_no_rewrite_and_fun_expressions_do() {
    let claim = Sentence::Claim {
        body: token("0"),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let bad_fun = rule_with_body(rewrite(
        token("0"),
        Term::apply("#fun2", vec![token("1"), token("2")]),
    ));
    let good_fun = rule_with_body(rewrite(
        token("0"),
        Term::apply("#fun2", vec![rewrite(token("1"), token("2")), token("3")]),
    ));
    let diagnostics = check_rewrites(&[&claim, &bad_fun, &good_fun]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "#fun expressions must have at least one rewrite."
    );
}

#[test]
fn function_context_rejects_rewrites_and_nesting() {
    let context_rewrite = rule_with_body(Term::apply(
        "#withConfig",
        vec![token("0"), rewrite(token("1"), token("2"))],
    ));
    let nested_context = rule_with_body(Term::apply(
        "#withConfig",
        vec![
            token("0"),
            Term::apply("#withConfig", vec![token("1"), token("2")]),
        ],
    ));
    let context_in_rewrite = rule_with_body(rewrite(
        token("0"),
        Term::apply("#withConfig", vec![token("1"), token("2")]),
    ));
    let diagnostics = check_rewrites(&[&context_rewrite, &nested_context, &context_in_rewrite]);

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Rewrites are not allowed in the context of a function rule."
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Function context is not allowed to be nested."
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Function context is not allowed inside a rewrite."
    }));
}

#[test]
fn anonymous_check_warns_for_singletons_and_rejects_reused_named_underscores() {
    let sentence = Sentence::Rule {
        body: rewrite(
            Term::sequence([
                Term::variable("X"),
                Term::variable("_USED"),
                Term::variable("_"),
            ]),
            Term::sequence([Term::variable("_USED"), Term::variable("_")]),
        ),
        requires: truth(),
        ensures: truth(),
        attributes: located(),
    };
    let diagnostics = check_anonymous_variables(&[&sentence]);

    assert_eq!(diagnostics.len(), 2);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::UnusedVariable && diagnostic.message.contains("'X'")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::InvalidAnonymousVariable
            && diagnostic.message.contains("'_USED'")
    }));
}

#[test]
fn anonymous_check_preserves_context_exemptions_and_generated_suppression() {
    let context = Sentence::Context {
        body: Term::variable("HOLE"),
        requires: truth(),
        attributes: located(),
    };
    let alias = Sentence::ContextAlias {
        body: Term::sequence([Term::variable("HOLE"), Term::variable("HERE")]),
        requires: truth(),
        attributes: located(),
    };
    let generated = rule_with_body(Term::variable("GENERATED"));

    assert!(check_anonymous_variables(&[&context, &alias, &generated]).is_empty());
}

#[test]
fn rhs_check_reports_unbound_variables_and_preserves_fresh_exceptions() {
    let sentence = rule_with_body(rewrite(
        Term::variable("X"),
        Term::sequence([
            Term::variable("X"),
            Term::variable("Y"),
            Term::variable("?FRESH"),
            Term::variable("!CONSTANT"),
            Term::variable("THIS_CONFIGURATION"),
        ]),
    ));
    let diagnostics = check_rhs_variables(
        &[&sentence],
        StructuralCheckOptions {
            symbolic: true,
            ..StructuralCheckOptions::default()
        },
    );

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::UnboundVariable);
    assert!(diagnostics[0].message.contains("variable Y"));
    assert!(diagnostics[0].message.contains("\"?Y\""));
}

#[test]
fn unbound_variables_attribute_allows_named_exceptions() {
    let sentence = Sentence::Rule {
        body: rewrite(
            token("0"),
            Term::sequence([
                Term::variable("A"),
                Term::variable("B"),
                Term::variable("_"),
            ]),
        ),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("unboundVariables", json!(" A, B, _ "))]),
    };

    assert!(check_rhs_variables(&[&sentence], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn requirements_bind_claim_and_haskell_variables_only() {
    let rule = Sentence::Rule {
        body: rewrite(token("0"), Term::variable("X")),
        requires: Term::variable("X"),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let claim = Sentence::Claim {
        body: rewrite(token("0"), Term::variable("X")),
        requires: Term::variable("X"),
        ensures: truth(),
        attributes: Attributes::default(),
    };

    let ordinary = check_rhs_variables(&[&rule], StructuralCheckOptions::default());
    let haskell = check_rhs_variables(
        &[&rule],
        StructuralCheckOptions {
            backend: StructuralCheckBackend::Haskell,
            ..StructuralCheckOptions::default()
        },
    );
    let claim = check_rhs_variables(&[&claim], StructuralCheckOptions::default());

    assert_eq!(ordinary.len(), 2);
    assert!(haskell.is_empty());
    assert!(claim.is_empty());
}

#[test]
fn concrete_mode_rejects_each_existential_occurrence() {
    let sentence = rule_with_body(rewrite(
        Term::variable("?X"),
        Term::sequence([Term::variable("?X"), Term::variable("?Y")]),
    ));
    let concrete = check_rhs_variables(&[&sentence], StructuralCheckOptions::default());
    let symbolic = check_rhs_variables(
        &[&sentence],
        StructuralCheckOptions {
            symbolic: true,
            ..StructuralCheckOptions::default()
        },
    );

    assert_eq!(
        concrete
            .iter()
            .filter(|diagnostic| {
                diagnostic.code == DiagnosticCode::UnsupportedExistentialVariable
            })
            .count(),
        3
    );
    assert!(symbolic.is_empty());
}

#[test]
fn ml_binders_bind_their_rhs_variables() {
    let sentence = rule_with_body(rewrite(
        token("0"),
        Term::apply(
            "#Exists",
            vec![
                Term::variable("X"),
                Term::apply("predicate", vec![Term::variable("X")]),
            ],
        ),
    ));

    assert!(check_rhs_variables(&[&sentence], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn semantic_casts_supply_variable_sort_context() {
    let typed = Term::Variable {
        name: "X".into(),
        sort: Some(Sort::new("Int")),
    };
    let cast = rule_with_body(rewrite(
        typed.clone(),
        Term::apply("#SemanticCastToInt", vec![Term::variable("X")]),
    ));
    let untyped = rule_with_body(rewrite(typed, Term::variable("X")));

    assert!(check_rhs_variables(&[&cast], StructuralCheckOptions::default()).is_empty());
    assert_eq!(
        check_rhs_variables(&[&untyped], StructuralCheckOptions::default()).len(),
        1
    );
}

#[test]
fn fun_in_pattern_and_in_k_special_cases_match_java() {
    let fun_pattern = rule_with_body(rewrite(
        Term::apply("#fun2", vec![rewrite(token("0"), token("1")), token("2")]),
        token("3"),
    ));
    let in_k = rule_with_body(rewrite(
        token("0"),
        Term::apply("_:=K_", vec![Term::variable("IGNORED"), token("1")]),
    ));
    let fun_diagnostics = check_rhs_variables(
        &[&fun_pattern],
        StructuralCheckOptions {
            symbolic: true,
            ..StructuralCheckOptions::default()
        },
    );

    assert_eq!(fun_diagnostics.len(), 1);
    assert_eq!(
        fun_diagnostics[0].code,
        DiagnosticCode::InvalidFunctionPattern
    );
    assert!(check_rhs_variables(&[&in_k], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn context_alias_hole_is_the_only_unbound_context_exception() {
    let alias = Sentence::ContextAlias {
        body: rewrite(token("0"), Term::variable("HOLE")),
        requires: truth(),
        attributes: Attributes::default(),
    };
    let context = Sentence::Context {
        body: rewrite(token("0"), Term::variable("HOLE")),
        requires: truth(),
        attributes: Attributes::default(),
    };

    assert!(check_rhs_variables(&[&alias], StructuralCheckOptions::default()).is_empty());
    assert_eq!(
        check_rhs_variables(&[&context], StructuralCheckOptions::default()).len(),
        1
    );
}

#[test]
fn module_runner_options_control_existential_policy() {
    let sentence = rule_with_body(rewrite(token("0"), Term::variable("?X")));
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![sentence],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let concrete = check_module(&resolved, resolved.main_module_id()).unwrap();
    let symbolic = check_module_with_options(
        &resolved,
        resolved.main_module_id(),
        StructuralCheckOptions {
            symbolic: true,
            ..StructuralCheckOptions::default()
        },
    )
    .unwrap();

    assert!(
        concrete.iter().any(|diagnostic| {
            diagnostic.code == DiagnosticCode::UnsupportedExistentialVariable
        })
    );
    assert!(
        !symbolic.iter().any(|diagnostic| {
            diagnostic.code == DiagnosticCode::UnsupportedExistentialVariable
        })
    );
}

fn rule_with_body(body: Term) -> Sentence {
    Sentence::Rule {
        body,
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    }
}
