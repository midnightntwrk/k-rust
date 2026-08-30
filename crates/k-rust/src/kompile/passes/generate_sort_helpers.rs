//! Generate sort predicates and projection functions consumed by later backend passes.

use serde_json::{Value, json};

use crate::{
    definition::{
        Attributes, Definition, LabelHead, ProductionItem, ResolvedDefinition, Sentence, SortHead,
    },
    kast::{Label, Sort, Term},
    provenance::{GeneratingPass, record_generated_origins},
};

use super::rebase_local_metadata;

/// Apply Java's `GenerateSortPredicateSyntax` transformation.
pub fn generate_sort_predicate_syntax(definition: &Definition) -> Result<Definition, String> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| error.to_string())?;
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let sorts = resolved.sort_catalog(module_id);
        let visible = resolved.sentences(module_id);
        let mut generated = Vec::new();
        for sort in sorts.local_sorts() {
            let label = Label::new(format!("is{sort}"));
            let production = Sentence::Production {
                label: Some(label.clone()),
                parameters: Vec::new(),
                sort: Sort::new("Bool"),
                items: vec![
                    ProductionItem::Terminal(label.name.clone()),
                    ProductionItem::Terminal("(".into()),
                    ProductionItem::NonTerminal {
                        sort: Sort::new("K"),
                        name: None,
                    },
                    ProductionItem::Terminal(")".into()),
                ],
                attributes: Attributes::new(
                    [
                        ("function".into(), Value::String(String::new())),
                        ("total".into(), Value::String(String::new())),
                        ("predicate".into(), sort_json(sort)),
                    ]
                    .into_iter()
                    .collect(),
                ),
            };
            if !visible.contains(&&production) && !module.local_sentences.contains(&production) {
                generated.push(production);
            }
        }
        if !generated.is_empty() {
            let k_sort = Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::new("K"),
                attributes: Attributes::default(),
            };
            if !module.local_sentences.contains(&k_sort) {
                generated.push(k_sort);
            }
            module.local_sentences.extend(generated);
        }
    }
    let output = rebase_local_metadata(definition, output)?;
    Ok(record_generated_origins(
        definition,
        output,
        GeneratingPass::GenerateSortPredicateSyntax,
    ))
}

/// Apply the non-coverage form of Java's `GenerateSortProjections` transformation.
pub fn generate_sort_projections(definition: &Definition) -> Result<Definition, String> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| error.to_string())?;
    let main_id = resolved.main_module_id();
    let main_productions = resolved.production_catalog(main_id);
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        let sorts = resolved.sort_catalog(module_id);
        let defined_labels = productions
            .defined_labels()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>();
        let local_productions = productions
            .productions()
            .filter(|(id, _)| productions.is_local(*id))
            .map(|(_, production)| production.clone())
            .collect::<Vec<_>>();
        let mut generated = Vec::new();
        for sort in sorts.all_sorts() {
            if is_parser_sort(sort) && !matches!(sort.name.as_str(), "K" | "KItem") {
                continue;
            }
            let label = Label::new(format!("project:{sort}"));
            if defined_labels.contains(&LabelHead::from(&label)) {
                continue;
            }
            generated.extend(sort_projection(sort, label));
        }
        for production in &local_productions {
            generated.extend(named_projections(
                production,
                &productions,
                &main_productions,
                &defined_labels,
            ));
        }
        for sentence in generated {
            if !module.local_sentences.contains(&sentence) {
                module.local_sentences.push(sentence);
            }
        }
    }
    let output = rebase_local_metadata(definition, output)?;
    Ok(record_generated_origins(
        definition,
        output,
        GeneratingPass::GenerateSortProjections,
    ))
}

fn sort_projection(sort: &Sort, label: Label) -> [Sentence; 2] {
    let variable = Term::Variable {
        name: "K".into(),
        sort: Some(sort.clone()),
    };
    let mut projection_attributes = Attributes::default();
    projection_attributes.insert("projection", json!(""));
    let mut production_attributes = projection_attributes.clone();
    production_attributes.insert("function", json!(""));
    [
        Sentence::Production {
            label: Some(label.clone()),
            parameters: Vec::new(),
            sort: sort.clone(),
            items: vec![
                ProductionItem::Terminal(label.name.clone()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("K"),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes: production_attributes,
        },
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::Apply {
                    label,
                    arguments: vec![variable.clone()],
                }),
                right: Box::new(variable),
            },
            requires: truth(),
            ensures: truth(),
            attributes: projection_attributes,
        },
    ]
}

fn named_projections(
    production: &Sentence,
    productions: &crate::definition::ProductionCatalog<'_>,
    main_productions: &crate::definition::ProductionCatalog<'_>,
    defined_labels: &std::collections::BTreeSet<LabelHead>,
) -> Vec<Sentence> {
    let Sentence::Production {
        label: Some(source_label),
        sort,
        items,
        attributes,
        ..
    } = production
    else {
        return Vec::new();
    };
    if attributes.get("function").is_some() || productions.macro_labels().contains(source_label) {
        return Vec::new();
    }
    let nonterminals = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, name } => Some((sort, name)),
            _ => None,
        })
        .collect::<Vec<_>>();
    if !nonterminals.iter().any(|(_, name)| name.is_some()) {
        return Vec::new();
    }
    if nonterminals
        .iter()
        .filter_map(|(_, name)| name.as_ref())
        .any(|name| {
            defined_labels.contains(&LabelHead::new(format!(
                "project:{}:{name}",
                source_label.name
            )))
        })
    {
        return Vec::new();
    }
    let total = main_productions
        .productions_for_sort(&SortHead::from(sort))
        .iter()
        .filter(|id| {
            !main_productions
                .production(**id)
                .attributes()
                .get("function")
                .is_some()
        })
        .count()
        == 1;
    let variables = nonterminals
        .iter()
        .enumerate()
        .map(|(index, (sort, _))| Term::Variable {
            name: format!("K{index}"),
            sort: Some((*sort).clone()),
        })
        .collect::<Vec<_>>();
    let mut generated = Vec::new();
    for (index, (field_sort, field_name)) in nonterminals.iter().enumerate() {
        let Some(field_name) = field_name else {
            continue;
        };
        let label = Label::new(format!("project:{}:{field_name}", source_label.name));
        let mut attributes = Attributes::default();
        attributes.insert("function", json!(""));
        if total {
            attributes.insert("total", json!(""));
        }
        generated.push(Sentence::Production {
            label: Some(label.clone()),
            parameters: Vec::new(),
            sort: (*field_sort).clone(),
            items: vec![
                ProductionItem::Terminal(field_name.clone()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: sort.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes,
        });
        generated.push(Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::Apply {
                    label,
                    arguments: vec![Term::Apply {
                        label: source_label.clone(),
                        arguments: variables.clone(),
                    }],
                }),
                right: Box::new(variables[index].clone()),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        });
    }
    generated
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn sort_json(sort: &Sort) -> Value {
    json!({
        "node": "KSort",
        "name": sort.name,
        "params": sort.parameters.iter().map(sort_json).collect::<Vec<_>>(),
    })
}

fn is_parser_sort(sort: &Sort) -> bool {
    matches!(
        sort.name.as_str(),
        "KBott" | "K" | "KLabel" | "KList" | "KItem" | "KConfigVar" | "KString"
    ) || sort.name.starts_with('#')
        || sort.name.parse::<u64>().is_ok()
}
