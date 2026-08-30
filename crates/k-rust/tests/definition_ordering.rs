use std::cmp::Ordering;
use std::collections::BTreeMap;

use k_rust::definition::{
    Associativity, Attributes, OrderingError, ProductionItem, SENTENCE_END_OFFSET_ATTRIBUTE,
    SENTENCE_START_OFFSET_ATTRIBUTE, Sentence, compare_attributes, compare_sentences,
    compare_terms, sentence_equivalent, sort_sentences,
};
use k_rust::kast::{Label, Sort, Term};
use k_rust::provenance::ORIGIN_ATTRIBUTE;
use serde_json::{Value, json};

fn attrs(entries: &[(&str, Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn empty() -> Attributes {
    Attributes::default()
}

fn variable(name: &str) -> Term {
    Term::variable(name)
}

fn sentence_name(sentence: &Sentence) -> &'static str {
    match sentence {
        Sentence::SyntaxSort { .. } => "KSyntaxSort",
        Sentence::SortSynonym { .. } => "KSortSynonym",
        Sentence::SyntaxLexical { .. } => "KSyntaxLexical",
        Sentence::Production { .. } => "KProduction",
        Sentence::SyntaxAssociativity { .. } => "KSyntaxAssociativity",
        Sentence::SyntaxPriority { .. } => "KSyntaxPriority",
        Sentence::ContextAlias { .. } => "KContextAlias",
        Sentence::Context { .. } => "KContext",
        Sentence::Rule { .. } => "KRule",
        Sentence::Claim { .. } => "KClaim",
        Sentence::Configuration { .. } => "KConfiguration",
        Sentence::Bubble { .. } => "KBubble",
    }
}

fn production(sort: &str, attributes: Attributes) -> Sentence {
    Sentence::Production {
        label: Some(Label::new("label")),
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: vec![ProductionItem::NonTerminal {
            sort: Sort::new("K"),
            name: None,
        }],
        attributes,
    }
}

#[test]
fn sorts_sentence_kinds_in_canonical_order() {
    let mut sentences = vec![
        Sentence::Bubble {
            sentence_type: "rule".into(),
            contents: "X".into(),
            attributes: empty(),
        },
        Sentence::Claim {
            body: variable("X"),
            requires: variable("R"),
            ensures: variable("E"),
            attributes: empty(),
        },
        Sentence::Rule {
            body: variable("X"),
            requires: variable("R"),
            ensures: variable("E"),
            attributes: empty(),
        },
        Sentence::Context {
            body: variable("X"),
            requires: variable("R"),
            attributes: empty(),
        },
        Sentence::ContextAlias {
            body: variable("X"),
            requires: variable("R"),
            attributes: empty(),
        },
        Sentence::SyntaxPriority {
            priorities: vec![vec!["tag".into()]],
            attributes: empty(),
        },
        Sentence::SyntaxAssociativity {
            associativity: Associativity::Left,
            tags: vec!["tag".into()],
            attributes: empty(),
        },
        production("K", empty()),
        Sentence::SyntaxLexical {
            name: "Id".into(),
            regex: "[a-z]+".into(),
            attributes: empty(),
        },
        Sentence::SortSynonym {
            new_sort: Sort::new("Nat"),
            old_sort: Sort::new("Int"),
            attributes: empty(),
        },
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("K"),
            attributes: empty(),
        },
    ];

    sort_sentences(&mut sentences).unwrap();
    assert_eq!(
        sentences.iter().map(sentence_name).collect::<Vec<_>>(),
        vec![
            "KSyntaxSort",
            "KSortSynonym",
            "KSyntaxLexical",
            "KProduction",
            "KSyntaxAssociativity",
            "KSyntaxPriority",
            "KContextAlias",
            "KContext",
            "KRule",
            "KClaim",
            "KBubble",
        ]
    );
}

#[test]
fn term_order_matches_scala_and_ignores_variable_sort() {
    let terms = [
        Term::InjectedLabel(Label::new("L")),
        Term::Rewrite {
            left: Box::new(variable("X")),
            right: Box::new(variable("Y")),
        },
        Term::As {
            pattern: Box::new(variable("X")),
            alias: Box::new(variable("Y")),
        },
        variable("X"),
        Term::Sequence(Vec::new()),
        Term::apply("f", Vec::new()),
        Term::Token {
            token: "x".into(),
            sort: Sort::new("K"),
        },
    ];
    for pair in terms.windows(2) {
        assert_eq!(compare_terms(&pair[0], &pair[1]), Ordering::Less);
    }

    assert_eq!(
        compare_terms(
            &Term::Variable {
                name: "X".into(),
                sort: Some(Sort::new("Int")),
            },
            &Term::Variable {
                name: "X".into(),
                sort: Some(Sort::new("Bool")),
            },
        ),
        Ordering::Equal
    );
}

#[test]
fn set_valued_syntax_fields_ignore_order_and_duplicates() {
    let associativity = |tags: &[&str]| Sentence::SyntaxAssociativity {
        associativity: Associativity::Left,
        tags: tags.iter().map(|tag| (*tag).into()).collect(),
        attributes: empty(),
    };
    let left = associativity(&["b", "a", "a"]);
    let right = associativity(&["a", "b"]);
    assert_eq!(compare_sentences(&left, &right).unwrap(), Ordering::Equal);
    assert!(sentence_equivalent(&left, &right));

    let priority = |tags: &[&str]| Sentence::SyntaxPriority {
        priorities: vec![tags.iter().map(|tag| (*tag).into()).collect()],
        attributes: empty(),
    };
    let left = priority(&["b", "a", "a"]);
    let right = priority(&["a", "b"]);
    assert_eq!(compare_sentences(&left, &right).unwrap(), Ordering::Equal);
    assert!(sentence_equivalent(&left, &right));
}

#[test]
fn preserves_scala_production_equality_and_ordering_divergence() {
    let location_one = attrs(&[("org.kframework.attributes.Location", json!([1, 1, 1, 2]))]);
    let location_two = attrs(&[("org.kframework.attributes.Location", json!([2, 1, 2, 2]))]);
    let int = production("Int", location_one.clone());
    let bool_at_other_location = production("Int", location_two);

    assert!(sentence_equivalent(&int, &bool_at_other_location));
    assert_ne!(
        compare_sentences(&int, &bool_at_other_location).unwrap(),
        Ordering::Equal
    );

    let different_sort = production("Bool", location_one);
    assert!(!sentence_equivalent(&int, &different_sort));
    assert_eq!(
        compare_sentences(&int, &different_sort).unwrap(),
        Ordering::Equal
    );

    let function = production("Int", attrs(&[("function", json!(""))]));
    let ordinary = production("Int", empty());
    assert!(!sentence_equivalent(&function, &ordinary));
}

#[test]
fn attribute_order_uses_scala_class_and_value_strings() {
    let line_ten = attrs(&[("org.kframework.attributes.Location", json!([10, 1, 10, 2]))]);
    let line_two = attrs(&[("org.kframework.attributes.Location", json!([2, 1, 2, 2]))]);
    assert_eq!(compare_attributes(&line_ten, &line_two), Ordering::Less);

    let sort_a = attrs(&[(
        "predicate",
        json!({"node": "KSort", "name": "A", "params": []}),
    )]);
    let sort_b = attrs(&[(
        "predicate",
        json!({"node": "KSort", "name": "B", "params": []}),
    )]);
    assert_eq!(compare_attributes(&sort_a, &sort_b), Ordering::Less);
}

#[test]
fn provenance_attributes_do_not_change_semantic_equality_or_ordering() {
    let ordinary = Sentence::Rule {
        body: variable("X"),
        requires: variable("R"),
        ensures: variable("E"),
        attributes: empty(),
    };
    let mut generated = ordinary.clone();
    generated.attributes_mut().insert(
        ORIGIN_ATTRIBUTE,
        json!({"pass": "macro-expansion", "origins": [], "destination": null}),
    );
    generated
        .attributes_mut()
        .insert(SENTENCE_START_OFFSET_ATTRIBUTE, json!(10));
    generated
        .attributes_mut()
        .insert(SENTENCE_END_OFFSET_ATTRIBUTE, json!(20));

    assert!(sentence_equivalent(&ordinary, &generated));
    assert_eq!(
        compare_sentences(&ordinary, &generated).unwrap(),
        Ordering::Equal,
    );
}

#[test]
fn configuration_is_intentionally_unorderable() {
    let configuration = Sentence::Configuration {
        body: variable("X"),
        ensures: variable("E"),
        attributes: empty(),
    };
    assert_eq!(
        compare_sentences(&configuration, &configuration),
        Err(OrderingError::UnorderableSentence("KConfiguration"))
    );

    let mut sentences = vec![
        Sentence::Bubble {
            sentence_type: "rule".into(),
            contents: "X".into(),
            attributes: empty(),
        },
        configuration,
    ];
    let original = sentences.clone();
    assert!(sort_sentences(&mut sentences).is_err());
    assert_eq!(sentences, original);
}
