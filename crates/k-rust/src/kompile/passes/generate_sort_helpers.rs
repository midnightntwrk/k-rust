//! ```toml algorithm
//! id = "kompile.sort_helpers.generate"
//! name = "generation of sort predicates, projections, and helper rules"
//! sites = ["generate_sort_predicate_syntax", "regenerate_sort_predicate_syntax", "generate_sort_projections"]
//! variable = "M = modules; S = visible sorts; V = visible sentences"
//! counters = []
//! no_counter = "sort-helper generation has no dedicated counter; the shared pass scaffolding bumps KompileResolveCalls, KompileSentenceCopies and KompilePartialOrdersBuilt, and KompileSentencesTransformed is added once per compile"
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(M x (S + V log V))"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Generate sort predicates and projection functions consumed by later backend passes.

use std::sync::Arc;

use crate::definition::ResolveError;
use serde_json::{Value, json};

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, LabelHead, ProductionItem, ResolvedDefinition, Sentence, SortHead,
        extend_with_new_sentences, retain_new_sentences,
    },
    kast::{FrontendSort, Label, Sort, Term},
    provenance::GeneratingPass,
};

/// Apply Java's `GenerateSortPredicateSyntax` transformation.
pub fn generate_sort_predicate_syntax(definition: &Definition) -> Result<Definition, ResolveError> {
    super::super::pipeline::run_standalone(
        definition,
        generate_sort_predicate_syntax_pass,
        Some(GeneratingPass::GenerateSortPredicateSyntax),
    )
}

pub(crate) fn generate_sort_predicate_syntax_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    Ok(generate_sort_predicate_syntax_from_resolved(
        input.definition,
        resolved,
    ))
}

fn generate_sort_predicate_syntax_from_resolved(
    definition: &Definition,
    resolved: &ResolvedDefinition,
) -> Definition {
    let views = resolved.views();
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let sorts = views.sort_catalog(module_id);
        let visible = resolved.sentences(module_id);
        let mut generated = Vec::new();
        // Predicate rules produce Boolean tokens even in standalone definitions.
        // Supply their token sort at the compilation root when the source does
        // not provide one. Imported prelude declarations remain authoritative.
        if module_id == resolved.main_module_id()
            && !sorts
                .token_sorts()
                .contains(&Sort::builtin(BuiltinSort::Bool))
        {
            let mut attributes = Attributes::default();
            attributes.mark(AttributeKey::Token);
            generated.push(Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::Bool),
                attributes,
            });
        }
        // Invariant: `generated` holds the optional `Bool` token sort and the sort predicate production of every sort of `sorts.local_sorts()` before `sort`; each iteration consumes one sort.
        for sort in sorts.local_sorts() {
            let label = Label::sort_predicate(sort);
            let production = Sentence::Production {
                label: Some(label.clone()),
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::Bool),
                items: vec![
                    ProductionItem::Terminal(label.name.clone()),
                    ProductionItem::Terminal("(".into()),
                    ProductionItem::NonTerminal {
                        sort: Sort::builtin(BuiltinSort::K),
                        name: None,
                    },
                    ProductionItem::Terminal(")".into()),
                ],
                attributes: Attributes::from_pairs([
                    (AttributeKey::Function, Value::String(String::new())),
                    (AttributeKey::Total, Value::String(String::new())),
                    (AttributeKey::Predicate, sort_json(sort)),
                ]),
            };
            generated.push(production);
        }
        let mut generated = retain_new_sentences(
            visible
                .iter()
                .copied()
                .chain(module.local_sentences.iter().map(Arc::as_ref)),
            generated,
        );
        if !generated.is_empty() {
            let k_sort = Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::K),
                attributes: Attributes::default(),
            };
            if !module
                .local_sentences
                .iter()
                .any(|sentence| **sentence == k_sort)
            {
                generated.push(k_sort);
            }
            module
                .local_sentences
                .extend(generated.into_iter().map(Arc::new));
        }
    }
    output
}

/// Restore generated sort predicates to their canonical unary signature after passes that may
/// temporarily add arguments, then generate predicates for any newly introduced sorts.
pub fn regenerate_sort_predicate_syntax(
    definition: &Definition,
) -> Result<Definition, ResolveError> {
    super::super::pipeline::run_standalone(definition, regenerate_sort_predicate_syntax_pass, None)
}

pub(crate) fn regenerate_sort_predicate_syntax_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            let sentence = crate::definition::sentence_mut(sentence);
            let Sentence::Production {
                label: Some(label),
                items,
                attributes,
                ..
            } = sentence
            else {
                continue;
            };
            if !attributes.has(AttributeKey::Predicate) {
                continue;
            }
            *items = vec![
                ProductionItem::Terminal(label.name.clone()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::builtin(BuiltinSort::K),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ];
        }
    }
    Ok(generate_sort_predicate_syntax_from_resolved(
        &output, resolved,
    ))
}

/// Apply the non-coverage form of Java's `GenerateSortProjections` transformation.
pub fn generate_sort_projections(definition: &Definition) -> Result<Definition, ResolveError> {
    super::super::pipeline::run_standalone(
        definition,
        generate_sort_projections_pass,
        Some(GeneratingPass::GenerateSortProjections),
    )
}

pub(crate) fn generate_sort_projections_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    let main_id = resolved.main_module_id();
    let views = resolved.views();
    let main_productions = views.production_catalog(main_id);
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        let sorts = views.sort_catalog(module_id);
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
        // Invariant: `generated` holds the projection production and rule of every sort of `sorts.all_sorts()` before `sort` that is not a parser sort (`K` and `KItem` excepted) and whose projection label is not in `defined_labels`; each iteration consumes one sort.
        for sort in sorts.all_sorts() {
            if is_parser_sort(sort)
                && sort.name != BuiltinSort::K.k_name()
                && sort.name != BuiltinSort::KItem.k_name()
            {
                continue;
            }
            let label = Label::projection(sort);
            if defined_labels.contains(&LabelHead::from(&label)) {
                continue;
            }
            generated.extend(sort_projection(sort, label));
        }
        // Invariant: `generated` also holds the named field projections of every production of `local_productions` before `production`; each iteration consumes one production.
        for production in &local_productions {
            // A field projection derives from the one production that names the field.
            generated.extend(
                named_projections(production, productions, main_productions, &defined_labels)
                    .into_iter()
                    .map(|mut projection| {
                        projection
                            .attributes_mut()
                            .union_input_addresses(production.attributes());
                        projection
                    }),
            );
        }
        extend_with_new_sentences(&mut module.local_sentences, generated);
    }
    Ok(output)
}

fn sort_projection(sort: &Sort, label: Label) -> [Sentence; 2] {
    let variable = Term::Variable {
        name: "K".into(),
        sort: Some(sort.clone()),
    };
    let mut projection_attributes = Attributes::default();
    projection_attributes.mark(AttributeKey::Projection);
    let mut production_attributes = projection_attributes.clone();
    production_attributes.mark(AttributeKey::Function);
    [
        Sentence::Production {
            label: Some(label.clone()),
            parameters: Vec::new(),
            sort: sort.clone(),
            items: vec![
                ProductionItem::Terminal(label.name.clone()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::builtin(BuiltinSort::K),
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
    // A bracket builds no term (the parsers erase it), so a projection through it would
    // mention a symbol that no term contains.
    if attributes.has(AttributeKey::Function)
        || attributes.has(AttributeKey::Bracket)
        || productions.macro_labels().contains(source_label)
    {
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
            defined_labels.contains(&LabelHead::new(
                Label::field_projection(&source_label.name, name).name,
            ))
        })
    {
        return Vec::new();
    }
    let total = main_productions
        .productions_for_sort(&SortHead::from(sort))
        .iter()
        .filter(|id| {
            let attributes = main_productions.production(**id).attributes();
            attributes.value(AttributeKey::Function).is_none()
                && !attributes.has(AttributeKey::Bracket)
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
    // Invariant: `generated` holds the projection production and rule of every named nonterminal of `nonterminals` before `index`; each iteration consumes one nonterminal.
    for (index, (field_sort, field_name)) in nonterminals.iter().enumerate() {
        let Some(field_name) = field_name else {
            continue;
        };
        let label = Label::field_projection(&source_label.name, field_name);
        let mut attributes = Attributes::default();
        attributes.mark(AttributeKey::Function);
        if total {
            attributes.mark(AttributeKey::Total);
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
        sort: Sort::builtin(BuiltinSort::Bool),
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
    [BuiltinSort::K, BuiltinSort::KItem, BuiltinSort::KConfigVar]
        .iter()
        .any(|builtin| sort.name == builtin.k_name())
        || [
            FrontendSort::KBott,
            FrontendSort::KLabel,
            FrontendSort::KList,
            FrontendSort::KString,
        ]
        .iter()
        .any(|frontend| sort.name == frontend.as_str())
        || sort.name.starts_with('#')
        || sort.name.parse::<u64>().is_ok()
}
