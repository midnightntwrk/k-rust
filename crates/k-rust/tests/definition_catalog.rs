use std::collections::BTreeMap;

use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, LabelHead, ProductionId, ProductionItem,
    ProductionSignature, ResolvedDefinition, Sentence, SortHead, sentence_equivalent,
};
use k_rust::kast::{Label, Sort};
use serde_json::Value;

fn attrs(keys: &[&str]) -> Attributes {
    Attributes::new(
        keys.iter()
            .map(|key| ((*key).into(), Value::String(String::new())))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn production(
    label: Option<Label>,
    parameters: Vec<Sort>,
    result: Sort,
    arguments: Vec<Sort>,
    attributes: Attributes,
) -> Sentence {
    let mut items = Vec::new();
    for (index, sort) in arguments.into_iter().enumerate() {
        if index != 0 {
            items.push(ProductionItem::Terminal(",".into()));
        }
        items.push(ProductionItem::NonTerminal { sort, name: None });
    }
    Sentence::Production {
        label,
        parameters,
        sort: result,
        items,
        attributes,
    }
}

fn label_of(sentence: &Sentence) -> Option<&str> {
    let Sentence::Production { label, .. } = sentence else {
        panic!("expected production")
    };
    label.as_ref().map(|label| label.name.as_str())
}

fn fixture() -> ResolvedDefinition {
    let variable = Sort::new("T");
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            production(
                Some(Label::with_parameters("f", vec![variable.clone()])),
                vec![variable.clone()],
                Sort::with_parameters("Box", vec![variable.clone()]),
                vec![variable],
                Attributes::default(),
            ),
            production(
                Some(Label::new("token")),
                Vec::new(),
                Sort::new("Int"),
                Vec::new(),
                attrs(&["token"]),
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
            production(
                Some(Label::new("f")),
                Vec::new(),
                Sort::with_parameters("Box", vec![Sort::new("Int")]),
                vec![Sort::new("Int")],
                Attributes::default(),
            ),
            production(
                Some(Label::new("fresh")),
                Vec::new(),
                Sort::new("Int"),
                vec![Sort::new("Int")],
                attrs(&["function"]),
            ),
            production(
                None,
                Vec::new(),
                Sort::new("Hidden"),
                Vec::new(),
                Attributes::default(),
            ),
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
fn assigns_dependency_first_ids_and_tracks_local_productions() {
    let resolved = fixture();
    let catalog = resolved.production_catalog(resolved.main_module_id());

    assert_eq!(catalog.len(), 5);
    assert_eq!(
        catalog
            .productions()
            .map(|(_, production)| label_of(production))
            .collect::<Vec<_>>(),
        [Some("f"), Some("token"), Some("f"), Some("fresh"), None]
    );
    assert_eq!(
        catalog.local_ids(),
        &[ProductionId(2), ProductionId(3), ProductionId(4)]
            .into_iter()
            .collect()
    );
    assert_eq!(catalog.local_productions().count(), 3);
    assert_eq!(
        catalog.local_labels(),
        [LabelHead::new("f"), LabelHead::new("fresh")]
            .into_iter()
            .collect()
    );
}

#[test]
fn indexes_label_and_sort_heads_without_losing_parameters() {
    let resolved = fixture();
    let catalog = resolved.production_catalog(resolved.main_module_id());

    assert_eq!(
        catalog.productions_for(&LabelHead::new("f")),
        [ProductionId(0), ProductionId(2)]
    );
    assert_eq!(
        catalog.productions_for_sort(&SortHead::new("Box")),
        [ProductionId(0), ProductionId(2)]
    );
    assert_eq!(catalog.defined_labels().count(), 3);
    assert_eq!(
        catalog.function_labels(),
        &[LabelHead::new("fresh")].into_iter().collect()
    );
    assert_eq!(
        catalog.token_productions_for(&Sort::new("Int")),
        [ProductionId(1)]
    );
}

#[test]
fn signatures_ignore_terminals_and_exclude_parametric_productions() {
    let resolved = fixture();
    let catalog = resolved.production_catalog(resolved.main_module_id());

    assert_eq!(
        catalog.signatures_for(&LabelHead::new("f")).unwrap(),
        &[ProductionSignature {
            arguments: vec![Sort::new("Int")],
            result: Sort::with_parameters("Box", vec![Sort::new("Int")]),
        }]
        .into_iter()
        .collect()
    );
    assert_eq!(
        catalog.signatures_for(&LabelHead::new("fresh")).unwrap(),
        &[ProductionSignature {
            arguments: vec![Sort::new("Int")],
            result: Sort::new("Int"),
        }]
        .into_iter()
        .collect()
    );
}

#[test]
fn sorted_ids_use_scala_order_with_a_deterministic_tie_breaker() {
    let first = production(
        Some(Label::new("z")),
        Vec::new(),
        Sort::new("Z"),
        Vec::new(),
        Attributes::default(),
    );
    let tied_first = production(
        Some(Label::new("same")),
        Vec::new(),
        Sort::new("First"),
        Vec::new(),
        Attributes::default(),
    );
    let tied_second = production(
        Some(Label::new("same")),
        Vec::new(),
        Sort::new("Second"),
        Vec::new(),
        Attributes::default(),
    );
    let last = production(
        Some(Label::new("a")),
        Vec::new(),
        Sort::new("A"),
        Vec::new(),
        Attributes::default(),
    );
    let catalog = k_rust::definition::ProductionCatalog::from_visible([
        &first,
        &tied_first,
        &tied_second,
        &last,
    ]);

    assert_eq!(
        catalog
            .sorted_ids()
            .iter()
            .map(|id| label_of(catalog.production(*id)).unwrap())
            .collect::<Vec<_>>(),
        ["a", "same", "same", "z"]
    );
    assert_eq!(
        catalog.sorted_ids()[1..3],
        [ProductionId(1), ProductionId(2)]
    );
    assert_eq!(catalog.sorted_productions().count(), 4);
}

#[test]
fn overloads_and_catalog_share_production_ids() {
    let resolved = fixture();
    let module = resolved.main_module_id();
    let catalog = resolved.production_catalog(module);
    let overloads = resolved.overloads(module).unwrap();

    assert_eq!(catalog.len(), overloads.catalog().len());
    for id in catalog.ids() {
        assert!(sentence_equivalent(
            catalog.production(id),
            overloads.production(id)
        ));
    }
}
