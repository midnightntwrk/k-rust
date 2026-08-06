use std::collections::{BTreeMap, BTreeSet};

use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, ProductionItem, ResolvedDefinition, Sentence,
    SortCatalog, SortHead,
};
use k_rust::kast::{Label, Sort};
use serde_json::{Value, json};

fn attrs(entries: &[(&str, Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn syntax_sort(parameters: Vec<Sort>, sort: Sort, attributes: Attributes) -> Sentence {
    Sentence::SyntaxSort {
        parameters,
        sort,
        attributes,
    }
}

fn production(
    result: Sort,
    parameters: Vec<Sort>,
    arguments: Vec<Sort>,
    attributes: Attributes,
) -> Sentence {
    Sentence::Production {
        label: Some(Label::new(format!("make{}", result.name))),
        parameters,
        sort: result,
        items: arguments
            .into_iter()
            .map(|sort| ProductionItem::NonTerminal { sort, name: None })
            .collect(),
        attributes,
    }
}

fn fixture() -> ResolvedDefinition {
    let int = Sort::new("Int");
    let variable = Sort::new("T");
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            syntax_sort(
                Vec::new(),
                int.clone(),
                attrs(&[("hook", json!("INT.Int")), ("token", json!(""))]),
            ),
            production(
                Sort::new("TokenFromProduction"),
                Vec::new(),
                Vec::new(),
                attrs(&[("token", json!(""))]),
            ),
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
            syntax_sort(
                vec![variable.clone()],
                Sort::with_parameters("List", vec![variable.clone()]),
                Attributes::default(),
            ),
            production(
                Sort::with_parameters("List", vec![int.clone()]),
                Vec::new(),
                vec![int.clone()],
                attrs(&[("userList", json!(""))]),
            ),
            production(
                Sort::with_parameters("Map", vec![Sort::new("K"), Sort::new("V")]),
                vec![Sort::new("K"), Sort::new("V")],
                Vec::new(),
                Attributes::default(),
            ),
            syntax_sort(
                Vec::new(),
                Sort::with_parameters("Vec", vec![Sort::new("3")]),
                Attributes::default(),
            ),
            Sentence::SortSynonym {
                new_sort: Sort::new("Nat"),
                old_sort: int,
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    };
    ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![main, base],
        attributes: Attributes::default(),
    })
    .unwrap()
}

#[test]
fn merge_attributes_keeps_agreement_and_drops_conflicts() {
    let first = attrs(&[("same", json!(1)), ("conflict", json!("left"))]);
    let second = attrs(&[
        ("same", json!(1)),
        ("conflict", json!("right")),
        ("unique", json!(true)),
    ]);
    let merged = Attributes::merge([&first, &second]);

    assert_eq!(merged.get("same"), Some(&json!(1)));
    assert_eq!(merged.get("unique"), Some(&json!(true)));
    assert_eq!(merged.get("conflict"), None);
}

#[test]
fn sort_heads_include_parameter_arity() {
    let nullary = SortHead::nullary("Map");
    let binary = SortHead::new("Map", 2);
    assert_ne!(nullary, binary);
    assert_eq!(nullary.to_string(), "Map");
    assert_eq!(binary.to_string(), "Map{S0,S1}");
    assert_eq!(
        SortHead::from(&Sort::with_parameters(
            "Map",
            vec![Sort::new("K"), Sort::new("V")]
        )),
        binary
    );
}

#[test]
fn derives_concrete_instantiations_and_numeric_parameter_sorts() {
    let resolved = fixture();
    let catalog = resolved.sort_catalog(resolved.main_module_id());

    assert_eq!(
        catalog.instantiations()[&SortHead::new("List", 1)],
        [Sort::with_parameters("List", vec![Sort::new("Int")])]
            .into_iter()
            .collect()
    );
    assert!(catalog.instantiations()[&SortHead::new("Map", 2)].is_empty());
    assert_eq!(
        catalog.instantiations()[&SortHead::new("Vec", 1)],
        [Sort::with_parameters("Vec", vec![Sort::new("3")])]
            .into_iter()
            .collect()
    );
    assert!(catalog.defined_heads().contains(&SortHead::nullary("3")));
    assert!(catalog.all_sorts().contains(&Sort::new("3")));
    assert!(!catalog.all_sorts().contains(&Sort::with_parameters(
        "Map",
        vec![Sort::new("K"), Sort::new("V")]
    )));
}

#[test]
fn derives_synonym_hook_token_and_list_views() {
    let resolved = fixture();
    let catalog = resolved.sort_catalog(resolved.main_module_id());

    assert_eq!(
        catalog.synonym_map().get(&Sort::new("Nat")),
        Some(&Sort::new("Int"))
    );
    assert_eq!(catalog.hooks().get("Int"), Some(&"INT.Int".into()));
    assert_eq!(
        catalog.token_sorts(),
        &[Sort::new("Int"), Sort::new("TokenFromProduction"),]
            .into_iter()
            .collect()
    );
    assert_eq!(
        catalog.list_sorts(),
        &[Sort::with_parameters("List", vec![Sort::new("Int")])]
            .into_iter()
            .collect()
    );
}

#[test]
fn local_sorts_exclude_every_sort_visible_through_direct_imports() {
    let resolved = fixture();
    let catalog = resolved.sort_catalog(resolved.main_module_id());

    assert!(!catalog.local_sorts().contains(&Sort::new("Int")));
    assert!(
        !catalog
            .local_sorts()
            .contains(&Sort::new("TokenFromProduction"))
    );
    assert!(
        catalog
            .local_sorts()
            .contains(&Sort::with_parameters("List", vec![Sort::new("Int")])),
    );
    assert_eq!(
        catalog.sorted_all_sorts().cloned().collect::<BTreeSet<_>>(),
        catalog.all_sorts().clone()
    );
}

#[test]
fn conflicting_sort_hooks_are_removed_by_attribute_merge() {
    let left = syntax_sort(
        Vec::new(),
        Sort::new("Conflict"),
        attrs(&[("hook", json!("LEFT.Hook"))]),
    );
    let right = syntax_sort(
        Vec::new(),
        Sort::new("Conflict"),
        attrs(&[("hook", json!("RIGHT.Hook"))]),
    );
    let catalog = SortCatalog::from_visible([&left, &right]);

    assert_eq!(
        catalog
            .declarations_for(&SortHead::nullary("Conflict"))
            .len(),
        2
    );
    assert_eq!(
        catalog
            .attributes_for(&SortHead::nullary("Conflict"))
            .unwrap()
            .get("hook"),
        None
    );
    assert!(!catalog.hooks().contains_key("Conflict"));
}
