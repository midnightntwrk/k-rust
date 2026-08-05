use k_rust::kast::ast::{Label, Sort, Term};
use k_rust::kast::{json, parser};
use proptest::prelude::*;

fn sort() -> impl Strategy<Value = Sort> {
    "[#A-Z][A-Za-z0-9]{0,7}"
        .prop_map(Sort::new)
        .prop_recursive(3, 32, 3, |inner| {
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

fn json_term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        (any::<String>(), sort()).prop_map(|(token, sort)| Term::Token { token, sort }),
        ("[A-Z_][A-Za-z0-9_']{0,7}", prop::option::of(sort()))
            .prop_map(|(name, sort)| Term::Variable { name, sort }),
        label().prop_map(Term::InjectedLabel),
    ];
    leaf.prop_recursive(5, 128, 8, |inner| {
        prop_oneof![
            (label(), prop::collection::vec(inner.clone(), 0..4))
                .prop_map(|(label, arguments)| Term::Apply { label, arguments }),
            prop::collection::vec(inner.clone(), 0..4).prop_map(Term::Sequence),
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

fn text_term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        (any::<String>(), sort()).prop_map(|(token, sort)| Term::Token { token, sort }),
        "[A-Z_][A-Za-z0-9_']{0,7}".prop_map(Term::variable),
        label().prop_map(Term::InjectedLabel),
    ];
    leaf.prop_recursive(4, 96, 6, |inner| {
        prop_oneof![
            (label(), prop::collection::vec(inner.clone(), 0..4))
                .prop_map(|(label, arguments)| Term::Apply { label, arguments }),
            prop_oneof![Just(Vec::new()), prop::collection::vec(inner, 2..4),]
                .prop_map(Term::sequence),
        ]
    })
}

fn text_normalize(term: Term) -> Term {
    match term {
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments.into_iter().map(text_normalize).collect(),
        },
        Term::Sequence(items) => {
            let mut flattened = Vec::new();
            for item in items.into_iter().map(text_normalize) {
                match item {
                    Term::Sequence(nested) => flattened.extend(nested),
                    item => flattened.push(item),
                }
            }
            match flattened.as_slice() {
                [item] => item.clone(),
                _ => Term::Sequence(flattened),
            }
        }
        term => term,
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn json_v4_round_trip(term in json_term()) {
        let encoded = json::to_string(&term).unwrap();
        prop_assert_eq!(json::from_str(&encoded).unwrap(), term);
    }

    #[test]
    fn textual_kast_round_trip(term in text_term()) {
        let printed = term.to_string();
        prop_assert_eq!(parser::parse_term(&printed).unwrap(), text_normalize(term));
    }
}
