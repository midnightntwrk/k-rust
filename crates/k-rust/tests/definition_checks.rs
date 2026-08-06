use std::collections::{BTreeMap, BTreeSet};

use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, LOCATION_ATTRIBUTE,
    PartialOrder, ProductionItem, SOURCE_ATTRIBUTE, Sentence, check_associativity,
    check_duplicate_labels, check_module, check_sort_top_uniqueness, check_syntax_groups,
    check_tokens, compute_priorities,
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
