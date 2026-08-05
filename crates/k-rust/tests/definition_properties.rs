use k_rust::definition::json;
use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ProductionItem, Sentence,
};
use k_rust::kast::{Label, Sort, Term};
use proptest::prelude::*;
use serde_json::Value;

fn sort() -> impl Strategy<Value = Sort> {
    "[#A-Z][A-Za-z0-9]{0,7}"
        .prop_map(Sort::new)
        .prop_recursive(2, 16, 2, |inner| {
            ("[#A-Z][A-Za-z0-9]{0,7}", prop::collection::vec(inner, 1..3))
                .prop_map(|(name, parameters)| Sort { name, parameters })
        })
}

fn label() -> impl Strategy<Value = Label> {
    (
        "[A-Za-z_#][A-Za-z0-9_+*'-]{0,9}",
        prop::collection::vec(sort(), 0..3),
    )
        .prop_map(|(name, parameters)| Label { name, parameters })
}

fn term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        (any::<String>(), sort()).prop_map(|(token, sort)| Term::Token { token, sort }),
        ("[A-Z_][A-Za-z0-9_']{0,7}", prop::option::of(sort()))
            .prop_map(|(name, sort)| Term::Variable { name, sort }),
        label().prop_map(Term::InjectedLabel),
    ];
    leaf.prop_recursive(3, 48, 5, |inner| {
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

fn attributes() -> impl Strategy<Value = Attributes> {
    let value = prop_oneof![
        any::<String>().prop_map(Value::String),
        prop::collection::vec(0_u16..1000, 0..5)
            .prop_map(|values| Value::Array(values.into_iter().map(Value::from).collect())),
    ];
    prop::collection::btree_map("[A-Za-z][A-Za-z0-9.]{0,15}", value, 0..5).prop_map(Attributes::new)
}

fn production_item() -> impl Strategy<Value = ProductionItem> {
    prop_oneof![
        (
            sort(),
            prop::option::of("[a-z][A-Za-z0-9]{0,7}".prop_map(String::from))
        )
            .prop_map(|(sort, name)| ProductionItem::NonTerminal { sort, name }),
        (
            prop::option::of(any::<String>()),
            any::<String>(),
            prop::option::of(any::<String>()),
        )
            .prop_map(|(precede_regex, regex, follow_regex)| {
                ProductionItem::RegexTerminal {
                    precede_regex,
                    regex,
                    follow_regex,
                }
            }),
        any::<String>().prop_map(ProductionItem::Terminal),
    ]
}

fn sentence() -> impl Strategy<Value = Sentence> {
    let syntax = prop_oneof![
        (prop::collection::vec(sort(), 0..3), sort(), attributes()).prop_map(
            |(parameters, sort, attributes)| Sentence::SyntaxSort {
                parameters,
                sort,
                attributes,
            }
        ),
        (sort(), sort(), attributes()).prop_map(|(new_sort, old_sort, attributes)| {
            Sentence::SortSynonym {
                new_sort,
                old_sort,
                attributes,
            }
        }),
        (any::<String>(), any::<String>(), attributes()).prop_map(|(name, regex, attributes)| {
            Sentence::SyntaxLexical {
                name,
                regex,
                attributes,
            }
        }),
        (
            prop::option::of(label()),
            prop::collection::vec(sort(), 0..3),
            sort(),
            prop::collection::vec(production_item(), 0..5),
            attributes(),
        )
            .prop_map(|(label, parameters, sort, items, attributes)| {
                Sentence::Production {
                    label,
                    parameters,
                    sort,
                    items,
                    attributes,
                }
            }),
        (
            prop_oneof![
                Just(Associativity::Left),
                Just(Associativity::Right),
                Just(Associativity::NonAssoc),
                Just(Associativity::Unspecified),
            ],
            prop::collection::vec(any::<String>(), 0..4),
            attributes(),
        )
            .prop_map(|(associativity, tags, attributes)| {
                Sentence::SyntaxAssociativity {
                    associativity,
                    tags,
                    attributes,
                }
            }),
        (
            prop::collection::vec(prop::collection::vec(any::<String>(), 0..3), 0..4),
            attributes(),
        )
            .prop_map(|(priorities, attributes)| Sentence::SyntaxPriority {
                priorities,
                attributes,
            }),
        (any::<String>(), any::<String>(), attributes()).prop_map(
            |(sentence_type, contents, attributes)| Sentence::Bubble {
                sentence_type,
                contents,
                attributes,
            }
        ),
    ];

    let semantic = prop_oneof![
        (term(), term(), attributes()).prop_map(|(body, requires, attributes)| {
            Sentence::Context {
                body,
                requires,
                attributes,
            }
        }),
        (term(), term(), term(), attributes()).prop_map(|(body, requires, ensures, attributes)| {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            }
        }),
        (term(), term(), term(), attributes()).prop_map(|(body, requires, ensures, attributes)| {
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            }
        }),
        (term(), term(), attributes()).prop_map(|(body, ensures, attributes)| {
            Sentence::Configuration {
                body,
                ensures,
                attributes,
            }
        }),
    ];

    prop_oneof![syntax, semantic]
}

fn definition() -> impl Strategy<Value = Definition> {
    (
        prop::collection::vec(sentence(), 0..12),
        attributes(),
        any::<bool>(),
    )
        .prop_map(|(local_sentences, attributes, public)| Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: vec![FlatImport {
                    name: "PRELUDE".into(),
                    public,
                }],
                local_sentences,
                attributes: Attributes::default(),
            }],
            attributes,
        })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn definition_json_v4_round_trip(definition in definition()) {
        let encoded = json::to_string(&definition).unwrap();
        prop_assert_eq!(json::from_str(&encoded).unwrap(), definition);
    }
}
