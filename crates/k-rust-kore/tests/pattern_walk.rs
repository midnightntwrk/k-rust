use k_rust_kore::kore::{
    ast::{Pattern, Sort, Variable, VariableKind},
    binary, codec, json,
    parser::parse_pattern,
    walk,
};
use proptest::prelude::*;

fn variable(name: &str) -> Variable {
    Variable {
        kind: VariableKind::Element,
        name: name.into(),
        sort: Sort::Variable("S".into()),
    }
}

fn parsed(source: &str) -> Pattern {
    parse_pattern(source).expect("test KORE should parse")
}

#[test]
fn post_order_visits_children_before_their_parent() {
    let pattern = parsed(r"f{}(g{}(), h{}())");
    let mut text = Vec::new();
    walk::for_each_post_order(&pattern, |node| text.push(node.to_string()));
    assert_eq!(text, ["g{}()", "h{}()", "f{}(g{}(), h{}())"]);
}

#[test]
fn variables_include_binders_and_occurrences_count_them() {
    let x = variable("X");
    let pattern = Pattern::Exists {
        sort: Sort::Variable("S".into()),
        variable: x.clone(),
        body: Box::new(Pattern::Variable(x.clone())),
    };
    assert_eq!(pattern.variables().into_iter().collect::<Vec<_>>(), [x]);
    assert_eq!(pattern.variable_occurrences().values().sum::<usize>(), 2);
}

#[test]
fn free_variables_respect_nested_shadowing() {
    let x = variable("X");
    let y = variable("Y");
    let pattern = Pattern::Exists {
        sort: Sort::Variable("S".into()),
        variable: x.clone(),
        body: Box::new(Pattern::And {
            sort: Sort::Variable("S".into()),
            arguments: vec![Pattern::Variable(x), Pattern::Variable(y.clone())],
        }),
    };
    assert_eq!(
        pattern.free_variables().into_iter().collect::<Vec<_>>(),
        [y]
    );
}

#[test]
fn sort_variables_include_node_symbol_and_binder_sorts() {
    let pattern = parsed(r"\exists{R}(X:S,f{T}(X:S))");
    assert_eq!(
        pattern.sort_variables(),
        ["R", "S", "T"].map(str::to_owned).into()
    );
}

#[test]
fn leading_existentials_and_strip_exists_agree() {
    let pattern = parsed(r"\exists{S}(X:S{},\exists{S}(Y:S{},f{}()))");
    let (body, variables) = pattern.leading_existentials();
    assert_eq!(body, pattern.strip_exists());
    assert_eq!(
        variables
            .iter()
            .map(|v| v.name.as_str())
            .collect::<Vec<_>>(),
        ["X", "Y"]
    );
}

#[test]
fn conjunction_flattening_preserves_other_sorts() {
    let pattern = parsed(r"\and{S}(a{}(),\and{T}(b{}(),c{}()),\top{S}())");
    let parts = pattern.conjuncts_at(&Sort::Variable("S".into()));
    assert_eq!(
        parts.iter().map(ToString::to_string).collect::<Vec<_>>(),
        ["a{}()", r"\and{T}(b{}(), c{}())"]
    );
}

#[test]
fn disjunction_flattening_drops_bottom_at_the_selected_sort() {
    let pattern = parsed(r"\or{S}(a{}(),\or{S}(b{}(),\bottom{S}()))");
    let parts = pattern.disjuncts_at(&Sort::Variable("S".into()));
    assert_eq!(
        parts.iter().map(ToString::to_string).collect::<Vec<_>>(),
        ["a{}()", "b{}()"]
    );
}

#[test]
fn find_application_returns_the_innermost_leftmost_match() {
    let pattern = parsed(r"f{}(f{}(a{}()),f{}(b{}()))");
    let found = pattern
        .find_application(|symbol, _| symbol.name == "f")
        .unwrap();
    assert_eq!(found.to_string(), "f{}(a{}())");
}

proptest! {
    #[test]
    fn every_encoding_round_trips(name in "[a-z]{1,8}") {
        let pattern = parsed(&format!("{name}{{}}()"));
        let text = pattern.to_string().into_bytes();
        let json = json::to_string(&pattern).unwrap().into_bytes();
        let binary = binary::encode_term(&pattern).unwrap();
        prop_assert_eq!(codec::decode_bytes(&text).unwrap(), pattern.clone());
        prop_assert_eq!(codec::decode_bytes(&json).unwrap(), pattern.clone());
        prop_assert_eq!(codec::decode_bytes(&binary).unwrap(), pattern);
    }
}
