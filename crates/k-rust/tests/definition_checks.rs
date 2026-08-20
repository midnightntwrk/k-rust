use std::collections::{BTreeMap, BTreeSet};

use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, LOCATION_ATTRIBUTE,
    PartialOrder, ProductionCatalog, ProductionItem, ResolvedModule, SOURCE_ATTRIBUTE, Sentence,
    SortCatalog, StructuralCheckBackend, StructuralCheckOptions, check_anonymous_variables,
    check_associativity, check_attribute_semantics, check_attributes, check_configuration_cells,
    check_definition, check_duplicate_klabels, check_duplicate_labels,
    check_function_rule_attributes, check_functions, check_holes, check_k_terms, check_klabels,
    check_module, check_module_with_options, check_rewrites, check_rhs_variables, check_smt_lemmas,
    check_sort_top_uniqueness, check_streams, check_syntax_groups, check_tokens,
    compute_priorities,
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
fn requirements_bind_claim_and_symbolic_backend_variables_only() {
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
    let symbolic = check_rhs_variables(
        &[&rule],
        StructuralCheckOptions {
            backend: StructuralCheckBackend::Rust,
            ..StructuralCheckOptions::default()
        },
    );
    let claim = check_rhs_variables(&[&claim], StructuralCheckOptions::default());

    assert_eq!(ordinary.len(), 2);
    assert!(symbolic.is_empty());
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
fn semantic_casts_supply_bound_variable_sort_context() {
    let cast = |name| Term::apply("#SemanticCastToInt", vec![Term::variable(name)]);
    let sentence = rule_with_body(rewrite(cast("X"), cast("X")));

    assert!(check_rhs_variables(&[&sentence], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn semantic_cast_context_does_not_override_nested_typed_variables() {
    let init = Term::Variable {
        name: "Init".into(),
        sort: Some(Sort::new("Map")),
    };
    let rhs = Term::apply(
        "#SemanticCastToK",
        vec![Term::apply(
            "project:KItem",
            vec![Term::apply("Map:lookup", vec![init.clone(), token("$PGM")])],
        )],
    );
    let sentence = rule_with_body(rewrite(init, rhs));

    assert!(check_rhs_variables(&[&sentence], StructuralCheckOptions::default()).is_empty());
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

#[test]
fn functions_are_allowed_at_top_and_on_rhs_but_not_nested_on_lhs() {
    let function = production(
        Some("f"),
        "Int",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let wrapper = production(Some("wrap"), "Int", &["Int"], Attributes::default());
    let nested = rule_with_body(rewrite(
        Term::apply("wrap", vec![Term::apply("f", vec![token("0")])]),
        token("1"),
    ));
    let top = rule_with_body(rewrite(Term::apply("f", vec![token("0")]), token("1")));
    let rhs = rule_with_body(rewrite(
        Term::apply("wrap", vec![token("0")]),
        Term::apply("f", vec![token("1")]),
    ));
    let diagnostics = function_diagnostics(&[&nested, &top, &rhs], &[&function, &wrapper]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::IllegalFunctionOnLhs);
    assert!(diagnostics[0].message.contains("function symbol f"));
}

#[test]
fn simplification_rules_and_internal_labels_are_exempt() {
    let function = production(
        Some("f"),
        "Int",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let predicate = production(
        Some("isInt"),
        "Bool",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let wrapper = production(Some("wrap"), "Int", &["Int"], Attributes::default());
    let simplification = Sentence::Rule {
        body: rewrite(
            Term::apply("wrap", vec![Term::apply("f", vec![token("0")])]),
            token("1"),
        ),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("simplification", json!(""))]),
    };
    let internal = rule_with_body(rewrite(
        Term::apply("wrap", vec![Term::apply("isInt", vec![token("0")])]),
        token("1"),
    ));

    assert!(
        function_diagnostics(
            &[&simplification, &internal],
            &[&function, &predicate, &wrapper]
        )
        .is_empty()
    );
}

#[test]
fn collection_hooks_visit_only_java_matching_positions() {
    let function = production(
        Some("f"),
        "Int",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let map_element = production(
        Some("mapElement"),
        "Map",
        &["Int", "Int"],
        attrs(&[("function", json!("")), ("hook", json!("MAP.element"))]),
    );
    let set_element = production(
        Some("setElement"),
        "Set",
        &["Int"],
        attrs(&[("function", json!("")), ("hook", json!("SET.element"))]),
    );
    let list_update = production(
        Some("listUpdate"),
        "List",
        &["List", "Int", "Int"],
        attrs(&[("function", json!("")), ("hook", json!("LIST.update"))]),
    );
    let map_rule = rule_with_body(rewrite(
        Term::apply(
            "mapElement",
            vec![
                Term::apply("f", vec![token("0")]),
                Term::apply("f", vec![token("1")]),
            ],
        ),
        token("2"),
    ));
    let set_rule = rule_with_body(rewrite(
        Term::apply("setElement", vec![Term::apply("f", vec![token("0")])]),
        token("1"),
    ));
    let list_rule = rule_with_body(rewrite(
        Term::apply(
            "listUpdate",
            vec![
                Term::apply("f", vec![token("0")]),
                Term::apply("f", vec![token("1")]),
                Term::apply("f", vec![token("2")]),
            ],
        ),
        token("3"),
    ));
    let diagnostics = function_diagnostics(
        &[&map_rule, &set_rule, &list_rule],
        &[&function, &map_element, &set_element, &list_update],
    );

    assert_eq!(diagnostics.len(), 3);
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| { diagnostic.code == DiagnosticCode::IllegalFunctionOnLhs })
    );
}

#[test]
fn with_config_preserves_java_top_level_state() {
    let function = production(
        Some("f"),
        "Int",
        &["Int"],
        attrs(&[("function", json!(""))]),
    );
    let sentence = rule_with_body(Term::apply(
        "#withConfig",
        vec![
            Term::apply("f", vec![token("0")]),
            Term::apply("f", vec![token("1")]),
        ],
    ));
    let diagnostics = function_diagnostics(&[&sentence], &[&function]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::IllegalFunctionOnLhs);
}

#[test]
fn module_runner_uses_visible_function_metadata() {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            production(
                Some("f"),
                "Int",
                &["Int"],
                attrs(&[("function", json!(""))]),
            ),
            production(Some("wrap"), "Int", &["Int"], Attributes::default()),
        ],
        attributes: Attributes::default(),
    };
    let main = FlatModule {
        name: "MAIN".into(),
        imports: vec![FlatImport {
            name: "BASE".into(),
            public: true,
        }],
        local_sentences: vec![rule_with_body(rewrite(
            Term::apply("wrap", vec![Term::apply("f", vec![token("0")])]),
            token("1"),
        ))],
        attributes: Attributes::default(),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![main, base],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_module(&resolved, resolved.main_module_id()).unwrap();

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::IllegalFunctionOnLhs);
}

#[test]
fn strictness_checks_positions_semicolons_and_k_nonterminals() {
    let nullary = production(
        Some("nullary"),
        "Foo",
        &[],
        attrs(&[("strict", json!("1"))]),
    );
    let out_of_range = production(
        Some("unary"),
        "Foo",
        &["Foo"],
        attrs(&[("strict", json!("2"))]),
    );
    let bad_semicolons = production(
        Some("aliases"),
        "Foo",
        &["Foo"],
        attrs(&[("strict", json!("foo; bar; 1"))]),
    );
    let k_argument = production(Some("hot"), "Foo", &["K"], attrs(&[("strict", json!(""))]));
    let safe_argument = production(
        Some("safe"),
        "Foo",
        &["K", "KItem"],
        attrs(&[("strict", json!("2"))]),
    );
    let java_trailing_separators = production(
        Some("separator"),
        "Foo",
        &["K"],
        attrs(&[("strict", json!(";"))]),
    );
    let diagnostics = check_holes(&[
        &nullary,
        &out_of_range,
        &bad_semicolons,
        &k_argument,
        &safe_argument,
        &java_trailing_separators,
    ]);

    assert_eq!(diagnostics.len(), 4);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Cannot put a strict attribute on a production with no nonterminals"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message
            == "Expecting a number between 1 and 1, but found 2 as a strict position in [2]"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .starts_with("Invalid strict attribute containing invalid semicolons")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Cannot heat a nonterminal of sort K. Did you mean KItem?"
    }));
}

#[test]
fn contexts_reject_holes_cast_to_k_only() {
    let invalid = Sentence::Context {
        body: Term::apply("#SemanticCastToK", vec![Term::variable("HOLE")]),
        requires: truth(),
        attributes: Attributes::default(),
    };
    let valid = Sentence::Context {
        body: Term::apply("#SemanticCastToKItem", vec![Term::variable("HOLE")]),
        requires: truth(),
        attributes: Attributes::default(),
    };
    let diagnostics = check_holes(&[&invalid, &valid]);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidHole);
}

#[test]
fn stream_cells_require_list_contents_and_valid_shape() {
    let valid = cell_production(
        "validStream",
        "ValidStreamCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("MyList"),
            name: None,
        },
        attrs(&[("cell", json!("")), ("stream", json!("stdin"))]),
    );
    let wrong_sort = cell_production(
        "badStream",
        "BadStreamCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("Int"),
            name: None,
        },
        attrs(&[("cell", json!("")), ("stream", json!("stdout"))]),
    );
    let malformed = cell_production(
        "malformedStream",
        "MalformedStreamCell",
        ProductionItem::Terminal("contents".into()),
        attrs(&[("cell", json!("")), ("stream", json!("stderr"))]),
    );
    let subsorts = PartialOrder::new([(Sort::new("MyList"), Sort::new("List"))]).unwrap();
    let diagnostics = check_streams(&[&valid, &wrong_sort, &malformed], &subsorts);

    assert_eq!(diagnostics.len(), 2);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Wrong sort in streaming cell. Expected List, but found Int."
    }));
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message == "Illegal arguments for stream cell." })
    );
}

#[test]
fn configuration_cells_detect_duplicates_and_unsupported_bags() {
    let child = cell_production(
        "kCell",
        "KCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("K"),
            name: None,
        },
        attrs(&[("cell", json!(""))]),
    );
    let first = cell_production(
        "topCell",
        "TopCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("KCell"),
            name: None,
        },
        attrs(&[("cell", json!(""))]),
    );
    let duplicate = cell_production(
        "otherCell",
        "OtherCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("KCell"),
            name: None,
        },
        attrs(&[("cell", json!(""))]),
    );
    let bag = cell_production(
        "bagCell",
        "BagCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("Int"),
            name: None,
        },
        attrs(&[("cell", json!("")), ("multiplicity", json!("*"))]),
    );
    let set = cell_production(
        "setCell",
        "SetCell",
        ProductionItem::NonTerminal {
            sort: Sort::new("Int"),
            name: None,
        },
        attrs(&[
            ("cell", json!("")),
            ("multiplicity", json!("*")),
            ("type", json!("Set")),
        ]),
    );
    let production_catalog =
        ProductionCatalog::from_visible([&child, &first, &duplicate, &bag, &set]);
    let diagnostics =
        check_configuration_cells(&[&first, &duplicate, &bag, &set], &production_catalog);

    assert_eq!(diagnostics.len(), 2);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::DuplicateConfigurationCell
            && diagnostic.message == "Cell kCell found twice in configuration."
    }));
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == DiagnosticCode::UnsupportedCellBag })
    );
}

#[test]
fn module_runner_includes_production_shape_checks() {
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![production(
                Some("hot"),
                "Foo",
                &["K"],
                attrs(&[("strict", json!(""))]),
            )],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_module(&resolved, resolved.main_module_id()).unwrap();

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidHole);
}

fn function_diagnostics(
    sentences: &[&Sentence],
    productions: &[&Sentence],
) -> Vec<k_rust::diagnostic::Diagnostic> {
    let production_catalog = ProductionCatalog::from_visible(productions.iter().copied());
    let sort_catalog = SortCatalog::from_visible(productions.iter().copied());
    check_functions(sentences, &production_catalog, &sort_catalog)
}

fn cell_production(
    label: &str,
    sort: &str,
    contents: ProductionItem,
    attributes: Attributes,
) -> Sentence {
    Sentence::Production {
        label: Some(Label::new(label)),
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: vec![
            ProductionItem::Terminal(format!("<{label}>")),
            contents,
            ProductionItem::Terminal(format!("</{label}>")),
        ],
        attributes,
    }
}

fn rule_with_body(body: Term) -> Sentence {
    Sentence::Rule {
        body,
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    }
}

#[test]
fn klabel_checks_use_visible_productions_and_internal_labels() {
    let defined = production(Some("defined"), "Int", &[], Attributes::default());
    let parametric = Sentence::Production {
        label: Some(Label::with_parameters("parametric", vec![Sort::new("S")])),
        parameters: vec![Sort::new("S")],
        sort: Sort::new("S"),
        items: Vec::new(),
        attributes: Attributes::default(),
    };
    let missing = rule_with_body(rewrite(
        Term::Rewrite {
            left: Box::new(Term::apply("defined", Vec::new())),
            right: Box::new(Term::Apply {
                label: Label::with_parameters("parametric", vec![Sort::new("Int")]),
                arguments: Vec::new(),
            }),
        },
        Term::apply("missing", Vec::new()),
    ));
    let injected = rule_with_body(rewrite(
        Term::InjectedLabel(Label::new("alsoMissing")),
        Term::apply("isInt", vec![token("0")]),
    ));
    let claim = Sentence::Claim {
        body: rewrite(Term::apply("ignoredInClaims", Vec::new()), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let productions = ProductionCatalog::from_visible([&defined, &parametric]);
    let sorts = SortCatalog::from_visible([&defined, &parametric]);
    let diagnostics = check_klabels(&[&missing, &injected, &claim], &productions, &sorts);

    assert_eq!(diagnostics.len(), 2);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::UndefinedKLabel && diagnostic.message.contains("missing")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::UndefinedKLabel
            && diagnostic.message.contains("alsoMissing")
    }));
}

#[test]
fn duplicate_klabels_are_scoped_to_the_main_import_closure() {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            production(Some("dup"), "Int", &[], Attributes::default()),
            production(Some("#EmptyK"), "K", &[], Attributes::default()),
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
            production(Some("dup"), "Other", &[], Attributes::default()),
            production(Some("#EmptyK"), "K", &[], Attributes::default()),
        ],
        attributes: Attributes::default(),
    };
    let disconnected = FlatModule {
        name: "DISCONNECTED".into(),
        imports: Vec::new(),
        local_sentences: vec![production(
            Some("dup"),
            "Elsewhere",
            &[],
            Attributes::default(),
        )],
        attributes: Attributes::default(),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![disconnected, main, base],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_duplicate_klabels(&resolved);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::DuplicateKLabel);
    assert!(diagnostics[0].message.contains("dup"));
}

#[test]
fn function_rules_must_consistently_use_concrete_or_symbolic() {
    let function = production(Some("f"), "Int", &[], attrs(&[("function", json!(""))]));
    let concrete = Sentence::Rule {
        body: rewrite(Term::apply("f", Vec::new()), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("concrete", json!(""))]),
    };
    let ordinary = Sentence::Rule {
        body: rewrite(Term::apply("f", Vec::new()), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![function, concrete, ordinary],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_function_rule_attributes(&resolved);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].code,
        DiagnosticCode::InconsistentFunctionRuleAttributes
    );
    assert!(diagnostics[0].message.contains("non-concrete rules"));
}

#[test]
fn function_rule_policy_covers_symbolic_conflicts_and_consistent_sets() {
    let symbolic_function = production(
        Some("symbolicF"),
        "Int",
        &[],
        attrs(&[("function", json!(""))]),
    );
    let conflicting_function = production(
        Some("conflictingF"),
        "Int",
        &[],
        attrs(&[("function", json!(""))]),
    );
    let consistent_function = production(
        Some("consistentF"),
        "Int",
        &[],
        attrs(&[("function", json!(""))]),
    );
    let symbolic = Sentence::Rule {
        body: rewrite(Term::apply("symbolicF", Vec::new()), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("symbolic", json!(""))]),
    };
    let ordinary = Sentence::Rule {
        body: rewrite(Term::apply("symbolicF", Vec::new()), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };
    let conflicting = Sentence::Rule {
        body: rewrite(Term::apply("conflictingF", Vec::new()), token("2")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("concrete", json!("")), ("symbolic", json!(""))]),
    };
    let consistent_one = Sentence::Rule {
        body: rewrite(Term::apply("consistentF", Vec::new()), token("3")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("concrete", json!(""))]),
    };
    let consistent_two = Sentence::Rule {
        body: rewrite(Term::apply("consistentF", Vec::new()), token("4")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("concrete", json!(""))]),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                symbolic_function,
                conflicting_function,
                consistent_function,
                symbolic,
                ordinary,
                conflicting,
                consistent_one,
                consistent_two,
            ],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_function_rule_attributes(&resolved);

    assert_eq!(diagnostics.len(), 2);
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("non-symbolic rules"))
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Rule cannot be both concrete and symbolic in the same variable."
    }));
}

#[test]
fn simplification_rules_reject_overlapping_concrete_and_symbolic_variables() {
    let simplification = Sentence::Rule {
        body: rewrite(token("0"), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[
            ("simplification", json!("")),
            ("concrete", json!("X, Y")),
            ("symbolic", json!("Y, Z")),
        ]),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![simplification],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_function_rule_attributes(&resolved);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "Rule cannot be both concrete and symbolic in the same variable: [Y]"
    );
}

#[test]
fn simplification_rule_empty_attribute_overlap_preserves_java_rendering() {
    let simplification = Sentence::Rule {
        body: rewrite(token("0"), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[
            ("simplification", json!("")),
            ("concrete", json!("")),
            ("symbolic", json!("")),
        ]),
    };
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![simplification],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_function_rule_attributes(&resolved);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "Rule cannot be both concrete and symbolic in the same variable: []"
    );
}

#[test]
fn definition_runner_checks_every_module_and_definition_wide_invariants() {
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![
            FlatModule {
                name: "MAIN".into(),
                imports: vec![FlatImport {
                    name: "BASE".into(),
                    public: true,
                }],
                local_sentences: vec![production(Some("dup"), "Int", &[], Attributes::default())],
                attributes: Attributes::default(),
            },
            FlatModule {
                name: "BASE".into(),
                imports: Vec::new(),
                local_sentences: vec![
                    production(Some("dup"), "Int", &[], Attributes::default()),
                    production(Some("hot"), "Foo", &["K"], attrs(&[("strict", json!(""))])),
                ],
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    })
    .unwrap();
    let diagnostics = check_definition(&resolved).unwrap();
    let codes = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<BTreeSet<_>>();

    assert!(codes.contains(&DiagnosticCode::DuplicateKLabel));
    assert!(codes.contains(&DiagnosticCode::InvalidHole));
}

#[test]
fn attribute_registry_rejects_unknown_and_misplaced_attributes() {
    let sentence = Sentence::Rule {
        body: rewrite(token("0"), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[
            ("binder", json!("")),
            ("made-up", json!("value")),
            ("label", json!("bad label`")),
            (SOURCE_ATTRIBUTE, json!("attributes.k")),
            (LOCATION_ATTRIBUTE, json!([4, 2, 4, 20])),
        ]),
    };
    let module = ResolvedModule {
        name: "MAIN".into(),
        local_sentences: vec![sentence],
        attributes: attrs(&[("function", json!(""))]),
    };
    let diagnostics = check_attributes(&module);

    assert_eq!(diagnostics.len(), 4);
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidAttribute)
            .count(),
        3
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::UnrecognizedAttribute
            && diagnostic.message.contains("made-up")
            && diagnostic.source.as_deref() == Some("attributes.k")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Label 'bad label`' cannot contain whitespace or backticks."
    }));
}

#[test]
fn format_checks_exempt_only_internal_layout_and_line_marker_sorts() {
    let regex_item = ProductionItem::regex(".+");
    let production = |sort: &str| Sentence::Production {
        label: None,
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: vec![regex_item.clone()],
        attributes: Attributes::default(),
    };
    let diagnostics = |sentence: &Sentence| {
        let productions = ProductionCatalog::from_visible([sentence]);
        let sorts = SortCatalog::from_visible([sentence]);
        check_attribute_semantics(&[sentence], &productions, &sorts)
    };

    assert!(diagnostics(&production("#Layout")).is_empty());
    assert!(diagnostics(&production("#LineMarker")).is_empty());
    assert!(diagnostics(&production("Layout")).iter().any(|diagnostic| {
        diagnostic
            .message
            .starts_with("Expected format attribute on production")
    }));
}

#[test]
fn rule_attribute_interactions_match_check_att() {
    let function = production(Some("f"), "Int", &[], attrs(&[("function", json!(""))]));
    let ordinary = production(Some("g"), "Int", &[], Attributes::default());
    let non_executable = Sentence::Rule {
        body: rewrite(Term::apply("g", Vec::new()), token("0")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("non-executable", json!(""))]),
    };
    let simplification = Sentence::Rule {
        body: rewrite(Term::apply("f", Vec::new()), token("1")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[
            ("simplification", json!("")),
            ("owise", json!("")),
            ("priority", json!("50")),
            ("anywhere", json!("")),
            ("symbolic", json!("")),
        ]),
    };
    let syntactic = Sentence::Rule {
        body: rewrite(Term::apply("g", Vec::new()), token("2")),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("syntactic", json!("X"))]),
    };
    let production_catalog = ProductionCatalog::from_visible([&function, &ordinary]);
    let sort_catalog = SortCatalog::from_visible([&function, &ordinary]);
    let diagnostics = check_attribute_semantics(
        &[&non_executable, &simplification, &syntactic],
        &production_catalog,
        &sort_catalog,
    );

    assert_eq!(diagnostics.len(), 6);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("non-executable attribute is only supported")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("anywhere attribute is not supported on symbolic rules")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("syntactic attribute is only supported")
    }));
}

#[test]
fn hooked_sort_binder_and_bracket_checks_use_visible_sort_metadata() {
    let hooked_sort = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Hooked"),
        attributes: attrs(&[("hook", json!("TEST.Hooked"))]),
    };
    let variable_sort = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Name"),
        attributes: attrs(&[("hook", json!("STRING.String"))]),
    };
    let hooked_constructor = production(Some("newHooked"), "Hooked", &[], Attributes::default());
    let binder = production(
        Some("bind"),
        "Expr",
        &["Name", "Expr"],
        attrs(&[("binder", json!(""))]),
    );
    let bracket = production(
        Some("bracket"),
        "Expr",
        &["Other"],
        attrs(&[("bracket", json!(""))]),
    );
    let visible = [
        &hooked_sort,
        &variable_sort,
        &hooked_constructor,
        &binder,
        &bracket,
    ];
    let production_catalog = ProductionCatalog::from_visible(visible);
    let sort_catalog = SortCatalog::from_visible(visible);
    let diagnostics = check_attribute_semantics(
        &[&hooked_constructor, &binder, &bracket],
        &production_catalog,
        &sort_catalog,
    );

    assert_eq!(diagnostics.len(), 3);
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("Cannot add new constructors to hooked sort Hooked")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("First child of binder must have a sort")
    }));
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == DiagnosticCode::InvalidBracketProduction })
    );
}

#[test]
fn production_format_colors_and_deprecation_checks_match_java() {
    let missing_format = Sentence::Production {
        label: Some(Label::new("regex")),
        parameters: Vec::new(),
        sort: Sort::new("Token"),
        items: vec![ProductionItem::regex("[a-z]+")],
        attributes: Attributes::default(),
    };
    let unfinished = Sentence::Production {
        label: Some(Label::new("unfinished")),
        parameters: Vec::new(),
        sort: Sort::new("Expr"),
        items: vec![ProductionItem::Terminal("x".into())],
        attributes: attrs(&[("format", json!("%"))]),
    };
    let bad_index = Sentence::Production {
        label: Some(Label::new("badIndex")),
        parameters: Vec::new(),
        sort: Sort::new("Expr"),
        items: vec![ProductionItem::Terminal("x".into())],
        attributes: attrs(&[("format", json!("%0"))]),
    };
    let regex_index = Sentence::Production {
        label: Some(Label::new("regexIndex")),
        parameters: Vec::new(),
        sort: Sort::new("Expr"),
        items: vec![ProductionItem::regex("x")],
        attributes: attrs(&[("format", json!("%1"))]),
    };
    let colors = Sentence::Production {
        label: Some(Label::new("colors")),
        parameters: Vec::new(),
        sort: Sort::new("Expr"),
        items: vec![
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: Sort::new("Expr"),
                name: None,
            },
        ],
        attributes: attrs(&[("format", json!("%1%2")), ("colors", json!("red,blue"))]),
    };
    let deprecated = production(
        Some("legacy"),
        "Expr",
        &[],
        attrs(&[
            ("total", json!("")),
            ("terminator-symbol", json!(".Legacy")),
            ("functional", json!("")),
            ("latex", json!("legacy")),
        ]),
    );
    let visible = [
        &missing_format,
        &unfinished,
        &bad_index,
        &regex_index,
        &colors,
        &deprecated,
    ];
    let production_catalog = ProductionCatalog::from_visible(visible);
    let sort_catalog = SortCatalog::from_visible(visible);
    let diagnostics = check_attribute_semantics(&visible, &production_catalog, &sort_catalog);

    assert_eq!(diagnostics.len(), 9);
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::DeprecatedAttribute)
            .count(),
        2
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Invalid format attribute: unfinished escape sequence."
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("Invalid colors attribute: expected 1")
    }));
}

#[test]
fn symbol_migration_and_overload_attributes_are_checked_together() {
    let legacy = production(
        Some("legacy"),
        "Expr",
        &[],
        attrs(&[("klabel", json!("legacy")), ("symbol", json!(""))]),
    );
    let conflicting = production(
        Some("conflicting"),
        "Expr",
        &[],
        attrs(&[
            ("klabel", json!("old")),
            ("symbol", json!("new")),
            ("overload", json!("group")),
        ]),
    );
    let unlabeled_overload = production(None, "Expr", &[], attrs(&[("overload", json!("group"))]));
    let visible = [&legacy, &conflicting, &unlabeled_overload];
    let production_catalog = ProductionCatalog::from_visible(visible);
    let sort_catalog = SortCatalog::from_visible(visible);
    let diagnostics = check_attribute_semantics(&visible, &production_catalog, &sort_catalog);

    assert_eq!(diagnostics.len(), 4);
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Warning)
            .count(),
        1
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("cannot be combined with `klabel(_)`")
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("Production would not be a KORE symbol")
    }));
}

#[test]
fn smt_lemma_terms_require_smt_backed_visible_productions() {
    let good = production(
        Some("good"),
        "Bool",
        &["Bool"],
        attrs(&[("smt-hook", json!("good"))]),
    );
    let bad = production(Some("bad"), "Bool", &[], Attributes::default());
    let rule = Sentence::Rule {
        body: Term::apply(
            "good",
            vec![
                Term::apply("bad", Vec::new()),
                Term::apply("unknown", Vec::new()),
            ],
        ),
        requires: truth(),
        ensures: truth(),
        attributes: attrs(&[("smt-lemma", json!(""))]),
    };
    let productions = ProductionCatalog::from_visible([&good, &bad]);
    let diagnostics = check_smt_lemmas(&[&rule], &productions);

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidSmtLemma);
}
