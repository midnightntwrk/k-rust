use std::collections::BTreeMap;

use k_rust::definition::{
    Attributes, Definition, FlatModule, PartialOrder, ProductionId, ProductionItem,
    ResolvedDefinition, Sentence, compute_overloads, compute_subsorts,
};
use k_rust::kast::{Label, Sort};
use serde_json::Value;

fn attrs(entries: &[(&str, &str)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), Value::String((*value).into())))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn production(
    label: Option<&str>,
    result: &str,
    arguments: &[&str],
    attributes: Attributes,
) -> Sentence {
    Sentence::Production {
        label: label.map(Label::new),
        parameters: Vec::new(),
        sort: Sort::new(result),
        items: arguments
            .iter()
            .map(|sort| ProductionItem::NonTerminal {
                sort: Sort::new(*sort),
                name: None,
            })
            .collect(),
        attributes,
    }
}

fn id_with_result(overloads: &k_rust::definition::OverloadOrder<'_>, result: &str) -> ProductionId {
    overloads
        .productions()
        .find_map(|(id, sentence)| match sentence {
            Sentence::Production { sort, .. } if sort.name == result => Some(id),
            _ => None,
        })
        .unwrap()
}

#[test]
fn distinguishes_semantic_and_syntactic_subsorts() {
    let unlabeled = production(None, "Number", &["Int"], Attributes::default());
    let labeled = production(Some("asValue"), "Value", &["Number"], Attributes::default());
    let mut parametric = production(None, "Box", &["Value"], Attributes::default());
    let Sentence::Production { parameters, .. } = &mut parametric else {
        unreachable!()
    };
    parameters.push(Sort::new("T"));
    let non_injection = Sentence::Production {
        label: None,
        parameters: Vec::new(),
        sort: Sort::new("Value"),
        items: vec![
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: Sort::new("Int"),
                name: None,
            },
        ],
        attributes: Attributes::default(),
    };
    let sentences = [&unlabeled, &labeled, &parametric, &non_injection];

    let semantic = compute_subsorts(sentences, false).unwrap();
    assert!(semantic.less_than(&Sort::new("Int"), &Sort::new("Number")));
    assert!(!semantic.less_than(&Sort::new("Number"), &Sort::new("Value")));

    let syntactic = compute_subsorts(sentences, true).unwrap();
    assert!(syntactic.less_than(&Sort::new("Int"), &Sort::new("Value")));
    assert!(!syntactic.contains(&Sort::new("Box")));
}

#[test]
fn combines_explicit_and_legacy_overloads() {
    let subsorts = PartialOrder::new([
        (Sort::new("Int"), Sort::new("Number")),
        (Sort::new("Number"), Sort::new("Value")),
    ])
    .unwrap();
    let explicit_int = production(None, "Int", &["Int"], attrs(&[("overload", "numeric")]));
    let explicit_number = production(
        None,
        "Number",
        &["Number"],
        attrs(&[("overload", "numeric")]),
    );
    let legacy_number = production(Some("f"), "Number", &["Number"], Attributes::default());
    let legacy_value = production(Some("f"), "Value", &["Value"], Attributes::default());
    let unrelated = production(Some("g"), "Value", &["Value"], Attributes::default());

    let overloads = compute_overloads(
        [
            &explicit_int,
            &explicit_number,
            &legacy_number,
            &legacy_value,
            &unrelated,
        ],
        &subsorts,
    )
    .unwrap();
    let int = id_with_result(&overloads, "Int");
    let number_ids = overloads
        .productions()
        .filter_map(|(id, sentence)| match sentence {
            Sentence::Production { sort, .. } if sort.name == "Number" => Some(id),
            _ => None,
        })
        .collect::<Vec<_>>();
    let value_ids = overloads
        .productions()
        .filter_map(|(id, sentence)| match sentence {
            Sentence::Production { sort, label, .. }
                if sort.name == "Value"
                    && label.as_ref().is_some_and(|label| label.name == "f") =>
            {
                Some(id)
            }
            _ => None,
        })
        .collect::<Vec<_>>();

    assert!(
        number_ids
            .iter()
            .any(|number| overloads.order().less_than(&int, number))
    );
    assert!(number_ids.iter().any(|number| {
        value_ids
            .iter()
            .any(|value| overloads.order().less_than(number, value))
    }));
}

#[test]
fn overload_requires_matching_arity_and_at_least_one_strict_sort() {
    let subsorts = PartialOrder::new([(Sort::new("Int"), Sort::new("Number"))]).unwrap();
    let same_left = production(None, "Int", &["Int"], attrs(&[("overload", "same")]));
    let same_right = production(None, "Int", &["Int"], attrs(&[("overload", "same")]));
    let unary = production(None, "Int", &["Int"], attrs(&[("overload", "arity")]));
    let binary = production(
        None,
        "Number",
        &["Number", "Number"],
        attrs(&[("overload", "arity")]),
    );

    let overloads =
        compute_overloads([&same_left, &same_right, &unary, &binary], &subsorts).unwrap();
    assert_eq!(overloads.order().direct_relations().len(), 0);
}

#[test]
fn resolved_definition_derives_relations_from_visible_sentences() {
    let module = FlatModule {
        name: "MAIN".into(),
        imports: Vec::new(),
        local_sentences: vec![
            production(None, "Number", &["Int"], Attributes::default()),
            production(
                Some("intOp"),
                "Int",
                &["Int"],
                attrs(&[("overload", "numeric")]),
            ),
            production(
                Some("numberOp"),
                "Number",
                &["Number"],
                attrs(&[("overload", "numeric")]),
            ),
        ],
        attributes: Attributes::default(),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module],
        attributes: Attributes::default(),
    };
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let module = resolved.main_module_id();

    assert!(
        resolved
            .subsorts(module)
            .unwrap()
            .less_than(&Sort::new("Int"), &Sort::new("Number"))
    );
    assert_eq!(
        resolved
            .overloads(module)
            .unwrap()
            .order()
            .direct_relations()
            .len(),
        1
    );
}
