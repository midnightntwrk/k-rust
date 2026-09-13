use std::collections::BTreeMap;

use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ProductionItem,
    ResolvedDefinition, SENTENCE_END_OFFSET_ATTRIBUTE, SENTENCE_START_OFFSET_ATTRIBUTE, Sentence,
    sentence_equivalent, term_equivalent,
};
use k_rust::kast::{Label, Sort, Term, TermMetadata};
use k_rust::provenance::ORIGIN_ATTRIBUTE;
use proptest::prelude::*;
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
fn set_valued_syntax_fields_ignore_order_and_duplicates() {
    let associativity = |tags: &[&str]| Sentence::SyntaxAssociativity {
        associativity: Associativity::Left,
        tags: tags.iter().map(|tag| (*tag).into()).collect(),
        attributes: empty(),
    };
    assert!(sentence_equivalent(
        &associativity(&["b", "a", "a"]),
        &associativity(&["a", "b"])
    ));

    let priority = |tags: &[&str]| Sentence::SyntaxPriority {
        priorities: vec![tags.iter().map(|tag| (*tag).into()).collect()],
        attributes: empty(),
    };
    assert!(sentence_equivalent(
        &priority(&["b", "a", "a"]),
        &priority(&["a", "b"])
    ));
}

#[test]
fn production_equality_ignores_location_but_not_sort_or_function() {
    let location_one = attrs(&[("org.kframework.attributes.Location", json!([1, 1, 1, 2]))]);
    let location_two = attrs(&[("org.kframework.attributes.Location", json!([2, 1, 2, 2]))]);
    let int = production("Int", location_one.clone());
    let int_at_other_location = production("Int", location_two);
    assert!(sentence_equivalent(&int, &int_at_other_location));

    let different_sort = production("Bool", location_one);
    assert!(!sentence_equivalent(&int, &different_sort));

    let function = production("Int", attrs(&[("function", json!(""))]));
    let ordinary = production("Int", empty());
    assert!(!sentence_equivalent(&function, &ordinary));
}

#[test]
fn provenance_attributes_do_not_change_semantic_equality() {
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

    assert!(generated.attributes().is_empty());
    assert!(sentence_equivalent(&ordinary, &generated));
}

fn sort() -> impl Strategy<Value = Sort> {
    "[#A-Z][A-Za-z0-9]{0,5}"
        .prop_map(Sort::new)
        .prop_recursive(2, 12, 2, |inner| {
            ("[#A-Z][A-Za-z0-9]{0,5}", prop::collection::vec(inner, 1..3))
                .prop_map(|(name, parameters)| Sort { name, parameters })
        })
}

fn label() -> impl Strategy<Value = Label> {
    (
        "[A-Za-z_#][A-Za-z0-9_]{0,7}",
        prop::collection::vec(sort(), 0..3),
    )
        .prop_map(|(name, parameters)| Label { name, parameters })
}

fn term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        (any::<String>(), sort()).prop_map(|(token, sort)| Term::Token { token, sort }),
        ("[A-Z_][A-Za-z0-9_]{0,6}", prop::option::of(sort()))
            .prop_map(|(name, sort)| Term::Variable { name, sort }),
        label().prop_map(Term::InjectedLabel),
    ];
    leaf.prop_recursive(3, 40, 5, |inner| {
        prop_oneof![
            (label(), prop::collection::vec(inner.clone(), 0..3))
                .prop_map(|(label, arguments)| Term::Apply { label, arguments }),
            prop::collection::vec(inner.clone(), 0..3).prop_map(Term::Sequence),
            (inner.clone(), inner.clone()).prop_map(|(left, right)| Term::Rewrite {
                left: Box::new(left),
                right: Box::new(right),
            }),
            (inner.clone(), inner).prop_map(|(pattern, alias)| Term::As {
                pattern: Box::new(pattern),
                alias: Box::new(alias),
            }),
        ]
    })
}

fn sentence() -> impl Strategy<Value = Sentence> {
    (0_u8..11, "[A-Z][A-Za-z0-9]{0,5}", any::<u8>()).prop_map(|(kind, name, value)| {
        let attributes = Attributes::default();
        let variable = || Term::variable(name.clone());
        match kind {
            0 => Sentence::SyntaxSort {
                parameters: vec![Sort::new(format!("P{value}"))],
                sort: Sort::new(name),
                attributes,
            },
            1 => Sentence::SortSynonym {
                new_sort: Sort::new(name),
                old_sort: Sort::new(format!("S{value}")),
                attributes,
            },
            2 => Sentence::SyntaxLexical {
                name,
                regex: format!("[a-z]{{{value}}}"),
                attributes,
            },
            3 => Sentence::Production {
                label: Some(Label::new(name)),
                parameters: Vec::new(),
                sort: Sort::new(format!("S{value}")),
                items: vec![ProductionItem::Terminal(value.to_string())],
                attributes,
            },
            4 => Sentence::SyntaxAssociativity {
                associativity: match value % 4 {
                    0 => Associativity::Left,
                    1 => Associativity::Right,
                    2 => Associativity::NonAssoc,
                    _ => Associativity::Unspecified,
                },
                tags: vec![name, format!("T{value}")],
                attributes,
            },
            5 => Sentence::SyntaxPriority {
                priorities: vec![vec![name, format!("T{value}")]],
                attributes,
            },
            6 => Sentence::ContextAlias {
                body: variable(),
                requires: Term::variable(format!("R{value}")),
                attributes,
            },
            7 => Sentence::Context {
                body: variable(),
                requires: Term::variable(format!("R{value}")),
                attributes,
            },
            8 => Sentence::Rule {
                body: variable(),
                requires: Term::variable(format!("R{value}")),
                ensures: Term::variable(format!("E{value}")),
                attributes,
            },
            9 => Sentence::Claim {
                body: variable(),
                requires: Term::variable(format!("R{value}")),
                ensures: Term::variable(format!("E{value}")),
                attributes,
            },
            _ => Sentence::Bubble {
                sentence_type: name,
                contents: value.to_string(),
                attributes,
            },
        }
    })
}

/// The same term with every variable sort erased and every node wrapped in metadata.
fn erased_and_annotated(term: &Term) -> Term {
    let erased = match term {
        Term::InjectedLabel(label) => Term::InjectedLabel(label.clone()),
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(erased_and_annotated(left)),
            right: Box::new(erased_and_annotated(right)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(erased_and_annotated(pattern)),
            alias: Box::new(erased_and_annotated(alias)),
        },
        Term::Variable { name, .. } => Term::variable(name.clone()),
        Term::Sequence(items) => Term::Sequence(items.iter().map(erased_and_annotated).collect()),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(erased_and_annotated).collect(),
        },
        Term::Token { token, sort } => Term::Token {
            token: token.clone(),
            sort: sort.clone(),
        },
        Term::Annotated { term, .. } => erased_and_annotated(term),
    };
    erased.with_metadata(TermMetadata::default())
}

fn rule(body: Term) -> Sentence {
    Sentence::Rule {
        body,
        requires: Term::variable("R"),
        ensures: Term::variable("E"),
        attributes: Attributes::default(),
    }
}

/// The visible sentences of a module that imports one rule and declares another.
fn visible_rule_count(imported: Term, local: Term) -> usize {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![rule(imported)],
        attributes: Attributes::default(),
    };
    let main = FlatModule {
        name: "MAIN".into(),
        imports: vec![FlatImport {
            name: "BASE".into(),
            public: true,
        }],
        local_sentences: vec![rule(local)],
        attributes: Attributes::default(),
    };
    let resolved = ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![main, base],
        attributes: Attributes::default(),
    })
    .unwrap();
    resolved.sentences(resolved.main_module_id()).len()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn equivalence_is_reflexive_and_symmetric(left in sentence(), right in sentence()) {
        prop_assert!(sentence_equivalent(&left, &left));
        prop_assert_eq!(
            sentence_equivalent(&left, &right),
            sentence_equivalent(&right, &left),
        );
    }

    #[test]
    fn term_equivalence_ignores_annotations_and_variable_sorts(left in term(), right in term()) {
        prop_assert!(term_equivalent(&left, &left));
        prop_assert!(term_equivalent(&left, &erased_and_annotated(&left)));
        prop_assert_eq!(term_equivalent(&left, &right), term_equivalent(&right, &left));

        // Visible-sentence deduplication buckets rule bodies by a private key that must agree
        // with `term_equivalent`: equivalent bodies always share a bucket.
        prop_assert_eq!(visible_rule_count(left.clone(), erased_and_annotated(&left)), 1);
        prop_assert_eq!(
            visible_rule_count(left.clone(), right.clone()),
            if term_equivalent(&left, &right) { 1 } else { 2 },
        );
    }
}
