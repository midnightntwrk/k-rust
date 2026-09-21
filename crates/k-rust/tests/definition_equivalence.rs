use std::collections::BTreeMap;

use k_rust::definition::{
    Associativity, AttributeKey, Attributes, Definition, FlatImport, FlatModule, ProductionItem,
    ResolvedDefinition, SENTENCE_END_OFFSET_ATTRIBUTE, SENTENCE_START_OFFSET_ATTRIBUTE, Sentence,
    canonical_production_payload, production_identity, sentence_equivalent, term_equivalent,
};
use k_rust::kast::{Label, ProductionIdentity, Sort, Term, TermMetadata};
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
fn production_identity_hex_is_exact_lowercase_and_round_trips() {
    let identity = production_identity(&production("Int", empty())).unwrap();
    let encoded = identity.to_hex();
    assert_eq!(encoded.len(), 32);
    assert!(
        encoded
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    );
    assert_eq!(ProductionIdentity::from_hex(&encoded), Some(identity));
    assert_eq!(ProductionIdentity::from_hex(&encoded.to_uppercase()), None);
    assert_eq!(ProductionIdentity::from_hex(&encoded[..31]), None);
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

fn production_identity_case() -> impl Strategy<Value = (Sentence, Sentence, u8)> {
    (
        label(),
        prop::collection::vec(sort(), 0..3),
        sort(),
        sort(),
        prop::option::of("[a-z]{0,5}"),
        "[a-z]{0,5}",
        "[a-z]{0,5}",
        "[a-z]{0,5}",
        "[a-z]{0,5}",
        0_u8..10,
    )
        .prop_map(
            |(
                label,
                parameters,
                result,
                argument,
                argument_name,
                regex,
                terminal,
                klabel,
                function,
                mutation,
            )| {
                let mut attributes = Attributes::default();
                attributes.set(AttributeKey::Klabel, json!(klabel));
                attributes.set(AttributeKey::Function, json!(function));
                attributes.set(AttributeKey::Symbol, json!("symbol"));
                attributes.insert("ignored", json!("left"));
                let items = vec![
                    ProductionItem::NonTerminal {
                        sort: argument,
                        name: argument_name,
                    },
                    ProductionItem::RegexTerminal {
                        precede_regex: Some("left-precede".into()),
                        regex,
                        follow_regex: Some("left-follow".into()),
                    },
                    ProductionItem::Terminal(terminal),
                ];
                let left = Sentence::Production {
                    label: Some(label),
                    parameters,
                    sort: result,
                    items,
                    attributes,
                };
                let mut equivalent = left.clone();
                let Sentence::Production {
                    items, attributes, ..
                } = &mut equivalent
                else {
                    unreachable!()
                };
                let ProductionItem::RegexTerminal {
                    precede_regex,
                    follow_regex,
                    ..
                } = &mut items[1]
                else {
                    unreachable!()
                };
                *precede_regex = Some("right-precede".into());
                *follow_regex = Some("right-follow".into());
                attributes.insert("ignored", json!("right"));
                (left, equivalent, mutation)
            },
        )
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

fn visible_sentence_count(first: Sentence, second: Sentence) -> usize {
    let resolved = ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![first, second],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    })
    .unwrap();
    resolved.sentences(resolved.main_module_id()).len()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn equivalence_is_reflexive_symmetric_and_transitive(
        left in sentence(),
        middle in sentence(),
        right in sentence(),
    ) {
        prop_assert!(sentence_equivalent(&left, &left));
        prop_assert_eq!(
            sentence_equivalent(&left, &middle),
            sentence_equivalent(&middle, &left),
        );
        if sentence_equivalent(&left, &middle) && sentence_equivalent(&middle, &right) {
            prop_assert!(sentence_equivalent(&left, &right));
        }

        // Resolution's structural bucket may collide, but it must never separate equivalent
        // sentences before the exact predicate selects the retained representative.
        let equivalent = sentence_equivalent(&left, &middle);
        prop_assert_eq!(visible_sentence_count(left, middle), if equivalent { 1 } else { 2 });
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

    #[test]
    fn canonical_production_payload_matches_equivalence(
        (left, equivalent, mutation) in production_identity_case(),
    ) {
        prop_assert!(sentence_equivalent(&left, &equivalent));
        prop_assert_eq!(
            canonical_production_payload(&left),
            canonical_production_payload(&equivalent),
        );
        prop_assert_eq!(production_identity(&left), production_identity(&equivalent));

        let mut changed = left.clone();
        let Sentence::Production {
            label,
            parameters,
            sort,
            items,
            attributes,
        } = &mut changed
        else {
            unreachable!()
        };
        match mutation {
            0 => label.as_mut().unwrap().name.push('!'),
            1 => label.as_mut().unwrap().parameters.push(Sort::new("Changed")),
            2 => parameters.push(Sort::new("Changed")),
            3 => sort.name.push('!'),
            4 => {
                let ProductionItem::NonTerminal { name, .. } = &mut items[0] else {
                    unreachable!()
                };
                name.get_or_insert_default().push('!');
            }
            5 => {
                let ProductionItem::RegexTerminal { regex, .. } = &mut items[1] else {
                    unreachable!()
                };
                regex.push('!');
            }
            6 => {
                let ProductionItem::Terminal(text) = &mut items[2] else {
                    unreachable!()
                };
                text.push('!');
            }
            7 => {
                let changed = format!("{}!", attributes.string(AttributeKey::Klabel).unwrap());
                attributes.set(AttributeKey::Klabel, json!(changed));
            }
            8 => {
                let changed = format!("{}!", attributes.string(AttributeKey::Function).unwrap());
                attributes.set(AttributeKey::Function, json!(changed));
            }
            9 => {
                let changed = format!("{}!", attributes.string(AttributeKey::Symbol).unwrap());
                attributes.set(AttributeKey::Symbol, json!(changed));
            }
            _ => unreachable!(),
        }

        prop_assert!(!sentence_equivalent(&left, &changed));
        prop_assert_ne!(
            canonical_production_payload(&left),
            canonical_production_payload(&changed),
        );
        // A collision is theoretically possible; this generated test samples the compiler's
        // explicit SHA-256 collision-resistance assumption rather than proving it.
        prop_assert_ne!(production_identity(&left), production_identity(&changed));
    }
}
