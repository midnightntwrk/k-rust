//! Resolve fresh rule variables through per-sort generators and a counter cell.

use std::{collections::BTreeMap, collections::BTreeSet, fmt};

use serde_json::json;

use crate::{
    definition::{
        Attributes, Definition, LabelHead, ProductionCatalog, ProductionItem, ResolvedDefinition,
        Sentence, expand_configurations, sentence_equivalent,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term},
    provenance::{GeneratingPass, record_generated_origins},
};

use super::rebase_local_metadata_by;

const GENERATED_COUNTER_CELL: &str = "<generatedCounter>";
const GENERATED_COUNTER_SORT: &str = "GeneratedCounterCell";
const GENERATED_TOP_CELL: &str = "<generatedTop>";
const INIT_GENERATED_COUNTER_CELL: &str = "initGeneratedCounterCell";
const INIT_GENERATED_TOP_CELL: &str = "initGeneratedTopCell";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveFreshConstantsError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveFreshConstantsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "fresh constant resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveFreshConstantsError {}

/// Apply Java's `ResolveFreshConstants` definition transformation.
pub fn resolve_fresh_constants(
    definition: &Definition,
    initial_fresh: usize,
) -> Result<Definition, ResolveFreshConstantsError> {
    resolve_fresh_constants_inner(definition, initial_fresh).map(|output| {
        record_generated_origins(definition, output, GeneratingPass::ResolveFreshConstants)
    })
}

fn resolve_fresh_constants_inner(
    definition: &Definition,
    initial_fresh: usize,
) -> Result<Definition, ResolveFreshConstantsError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(|error| error_from(error.to_string()))?;
    let mut output = definition.clone();
    let mut diagnostics = Vec::new();

    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        let generators = match productions.fresh_generators() {
            Ok(generators) => generators,
            Err(error) => {
                diagnostics.push(plain_error(error.to_string()));
                continue;
            }
        };
        let visible_generated_top = productions
            .defined_labels()
            .any(|label| label.as_str() == GENERATED_TOP_CELL);
        let local_generated_top = productions
            .local_labels()
            .contains(&LabelHead::new(GENERATED_TOP_CELL));

        for sentence in &mut module.local_sentences {
            let original = sentence.clone();
            match transform_sentence(original, &productions, &generators) {
                Ok(transformed) => *sentence = transformed,
                Err(message) => diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidFreshConstant,
                    message,
                    sentence,
                )),
            }
        }

        let has_cells = productions
            .productions()
            .any(|(_, production)| production.attributes().get("cell").is_some());
        let configuration =
            if module.name == definition.main_module && !visible_generated_top && has_cells {
                match generated_top_configuration(&resolved, module_id, &productions, initial_fresh)
                {
                    Ok(configuration) => Some(configuration),
                    Err(message) => {
                        diagnostics.push(plain_error(message));
                        None
                    }
                }
            } else if local_generated_top {
                Some(counter_configuration(initial_fresh))
            } else {
                None
            };
        if let Some(configuration) = configuration {
            for sentence in counter_helpers() {
                if !module.local_sentences.contains(&sentence) {
                    module.local_sentences.push(sentence);
                }
            }
            module.local_sentences.push(configuration);
        }
        for sentence in &mut module.local_sentences {
            fix_generated_top_format(sentence);
        }
    }

    if !diagnostics.is_empty() {
        diagnostics.sort();
        diagnostics.dedup();
        return Err(ResolveFreshConstantsError { diagnostics });
    }

    let mut expanded =
        expand_configurations(&output).map_err(|error| error_from(error.to_string()))?;
    for module in &mut expanded.modules {
        for sentence in &mut module.local_sentences {
            fix_generated_top_format(sentence);
        }
    }
    rebase_local_metadata_by(definition, expanded, |source, target| {
        sentence_equivalent(source, target) || both_generated_top_productions(source, target)
    })
    .map_err(error_from)
}

fn transform_sentence(
    sentence: Sentence,
    productions: &ProductionCatalog<'_>,
    generators: &BTreeMap<Sort, Label>,
) -> Result<Sentence, String> {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } => {
            let original = Sentence::Rule {
                body: body.clone(),
                requires: requires.clone(),
                ensures: ensures.clone(),
                attributes: attributes.clone(),
            };
            let fresh = fresh_variables([&body, &requires, &ensures]);
            let offsets = fresh
                .keys()
                .enumerate()
                .map(|(offset, name)| (name.clone(), offset))
                .collect::<BTreeMap<_, _>>();
            let transformed_body = transform_term(body, &fresh, &offsets, generators)?;
            let with_fresh = Sentence::Rule {
                body: add_fresh_cell(transformed_body, fresh.len()),
                requires: transform_term(requires, &fresh, &offsets, generators)?,
                ensures: transform_term(ensures, &fresh, &offsets, generators)?,
                attributes,
            };
            if with_fresh.attributes().get("initializer").is_some()
                && rewrite_left(rule_body(&with_fresh))
                    .as_apply()
                    .is_some_and(|(label, _)| label.name == INIT_GENERATED_TOP_CELL)
            {
                return add_counter_initializer(with_fresh);
            }
            if rule_defines_function(&original, productions) {
                Ok(original)
            } else {
                Ok(with_fresh)
            }
        }
        Sentence::Context {
            body,
            requires,
            attributes,
        } => {
            let fresh = fresh_variables([&body, &requires]);
            let offsets = fresh
                .keys()
                .enumerate()
                .map(|(offset, name)| (name.clone(), offset))
                .collect::<BTreeMap<_, _>>();
            Ok(Sentence::Context {
                body: add_fresh_cell(
                    transform_term(body, &fresh, &offsets, generators)?,
                    fresh.len(),
                ),
                requires: transform_term(requires, &fresh, &offsets, generators)?,
                attributes,
            })
        }
        production @ Sentence::Production { .. } => Ok(add_counter_to_top_production(production)),
        sentence => Ok(sentence),
    }
}

fn fresh_variables<'a>(
    roots: impl IntoIterator<Item = &'a Term>,
) -> BTreeMap<String, Option<Sort>> {
    let mut fresh = BTreeMap::new();
    for root in roots {
        root.visit_preorder(&mut |term| {
            if let Term::Variable { name, sort } = term.unannotated()
                && name.starts_with('!')
            {
                let inferred = sort
                    .clone()
                    .or_else(|| term.metadata().and_then(|metadata| metadata.sort.clone()));
                fresh.entry(name.clone()).or_insert(inferred);
            }
        });
    }
    fresh
}

fn transform_term(
    term: Term,
    fresh: &BTreeMap<String, Option<Sort>>,
    offsets: &BTreeMap<String, usize>,
    generators: &BTreeMap<Sort, Label>,
) -> Result<Term, String> {
    let metadata = term.metadata().cloned();
    match term.into_unannotated() {
        Term::Variable { name, sort } if fresh.contains_key(&name) => {
            let sort = sort
                .or_else(|| metadata.and_then(|metadata| metadata.sort))
                .ok_or_else(|| "Fresh constant used without a declared sort.".to_owned())?;
            let generator = generators
                .get(&sort)
                .ok_or_else(|| format!("No fresh generator defined for sort {sort}"))?;
            Ok(Term::Apply {
                label: generator.clone(),
                arguments: vec![Term::apply(
                    "_+Int_",
                    vec![
                        fresh_counter(),
                        Term::Token {
                            token: offsets[&name].to_string(),
                            sort: Sort::new("Int"),
                        },
                    ],
                )],
            })
        }
        Term::Apply { label, arguments } => Ok(with_metadata(
            Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| transform_term(argument, fresh, offsets, generators))
                    .collect::<Result<_, _>>()?,
            },
            metadata,
        )),
        Term::Rewrite { left, right } => Ok(with_metadata(
            Term::Rewrite {
                left: Box::new(transform_term(*left, fresh, offsets, generators)?),
                right: Box::new(transform_term(*right, fresh, offsets, generators)?),
            },
            metadata,
        )),
        Term::As { pattern, alias } => Ok(with_metadata(
            Term::As {
                pattern: Box::new(transform_term(*pattern, fresh, offsets, generators)?),
                alias: Box::new(transform_term(*alias, fresh, offsets, generators)?),
            },
            metadata,
        )),
        Term::Sequence(items) => Ok(with_metadata(
            Term::Sequence(
                items
                    .into_iter()
                    .map(|item| transform_term(item, fresh, offsets, generators))
                    .collect::<Result<_, _>>()?,
            ),
            metadata,
        )),
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
            Ok(with_metadata(leaf, metadata))
        }
        Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    }
}

fn add_fresh_cell(body: Term, count: usize) -> Term {
    if count == 0 {
        return body;
    }
    Term::apply(
        "#cells",
        vec![
            body,
            incomplete_cell(
                GENERATED_COUNTER_CELL,
                false,
                Term::Rewrite {
                    left: Box::new(fresh_counter()),
                    right: Box::new(Term::apply(
                        "_+Int_",
                        vec![
                            fresh_counter(),
                            Term::Token {
                                token: count.to_string(),
                                sort: Sort::new("Int"),
                            },
                        ],
                    )),
                },
                false,
            ),
        ],
    )
}

fn rule_defines_function(sentence: &Sentence, productions: &ProductionCatalog<'_>) -> bool {
    let mut left = rewrite_left(rule_body(sentence));
    if let Some((label, arguments)) = left.as_apply()
        && label.name == "#withConfig"
        && let Some(first) = arguments.first()
    {
        left = first.clone();
    }
    left.as_apply().is_some_and(|(label, _)| {
        productions
            .function_labels()
            .contains(&LabelHead::from(label))
    })
}

fn add_counter_initializer(sentence: Sentence) -> Result<Sentence, String> {
    let Sentence::Rule {
        body,
        requires,
        ensures,
        attributes,
    } = sentence
    else {
        unreachable!()
    };
    let Term::Rewrite { left, right } = body.into_unannotated() else {
        return Err("Malformed generated top-cell initializer rule".into());
    };
    let Term::Apply {
        label,
        mut arguments,
    } = right.into_unannotated()
    else {
        return Err("Malformed generated top-cell initializer result".into());
    };
    let Some(body) = arguments.get_mut(1) else {
        return Err("Malformed generated top-cell initializer result".into());
    };
    let Term::Apply {
        label: cells_label,
        arguments: cells,
    } = body.unannotated()
    else {
        return Err("Malformed generated top-cell initializer contents".into());
    };
    let mut cells = cells.clone();
    cells.push(Term::apply(INIT_GENERATED_COUNTER_CELL, Vec::new()));
    *body = Term::Apply {
        label: cells_label.clone(),
        arguments: cells,
    };
    Ok(Sentence::Rule {
        body: Term::Rewrite {
            left,
            right: Box::new(Term::Apply { label, arguments }),
        },
        requires,
        ensures,
        attributes,
    })
}

fn add_counter_to_top_production(sentence: Sentence) -> Sentence {
    let Sentence::Production {
        label,
        parameters,
        sort,
        mut items,
        attributes,
    } = sentence
    else {
        unreachable!()
    };
    if label
        .as_ref()
        .is_some_and(|label| label.name == GENERATED_TOP_CELL)
        && !items.iter().any(|item| {
            matches!(
                item,
                ProductionItem::NonTerminal { sort, .. } if sort.name == GENERATED_COUNTER_SORT
            )
        })
    {
        let position = items.len().saturating_sub(1);
        items.insert(
            position,
            ProductionItem::NonTerminal {
                sort: Sort::new(GENERATED_COUNTER_SORT),
                name: None,
            },
        );
    }
    Sentence::Production {
        label,
        parameters,
        sort,
        items,
        attributes,
    }
}

fn fix_generated_top_format(sentence: &mut Sentence) {
    let Sentence::Production {
        label: Some(label),
        items,
        attributes,
        ..
    } = sentence
    else {
        return;
    };
    if label.name != GENERATED_TOP_CELL {
        return;
    }
    let positions = items
        .iter()
        .enumerate()
        .filter_map(|(index, item)| match item {
            ProductionItem::NonTerminal { sort, .. } if sort.name != GENERATED_COUNTER_SORT => {
                Some(index + 1)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let Some(last) = positions.last().copied() else {
        return;
    };
    let format = if positions.len() == 1 {
        format!("%{}", positions[0])
    } else {
        let mut format = String::from("%1%i");
        for position in positions {
            format.push_str(&format!("%n%{position}"));
        }
        format.push_str(&format!("%d%n%{}", last + 2));
        format
    };
    attributes.insert("format", json!(format));
}

fn generated_top_configuration(
    definition: &ResolvedDefinition,
    module: crate::definition::ModuleId,
    productions: &ProductionCatalog<'_>,
    initial_fresh: usize,
) -> Result<Sentence, String> {
    let root_sort = root_cell_sort(definition, module, productions)?;
    let root = productions
        .productions_for_sort(&crate::definition::SortHead::from(&root_sort))
        .iter()
        .find_map(|id| match productions.production(*id) {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.get("cell").is_some() => Some((label, attributes)),
            _ => None,
        })
        .ok_or_else(|| format!("No cell production found for root sort {root_sort}"))?;
    let cell_name = root
        .1
        .get_str("cellName")
        .ok_or_else(|| format!("Root cell {} has no cellName attribute", root.0.name))?;
    let name = cell_name_token("generatedTop");
    Ok(configuration(Term::apply(
        "#configCell",
        vec![
            name.clone(),
            Term::apply("#cellPropertyListTerminator", Vec::new()),
            Term::apply(
                "#cells",
                vec![
                    Term::apply("#externalCell", vec![cell_name_token(cell_name)]),
                    counter_config_term(initial_fresh),
                ],
            ),
            name,
        ],
    )))
}

fn root_cell_sort(
    definition: &ResolvedDefinition,
    module: crate::definition::ModuleId,
    productions: &ProductionCatalog<'_>,
) -> Result<Sort, String> {
    let cells = productions
        .productions()
        .filter_map(|(_, production)| match production {
            Sentence::Production {
                sort, attributes, ..
            } if attributes.get("cell").is_some() => Some(sort.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let collections = productions
        .productions()
        .filter_map(|(_, production)| match production {
            Sentence::Production {
                sort, attributes, ..
            } if attributes.get("cellCollection").is_some() => Some(sort.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let subsorts = definition
        .subsorts(module)
        .map_err(|error| error.to_string())?;
    let mut children = BTreeSet::new();
    for (_, production) in productions.productions() {
        let Sentence::Production {
            sort,
            items,
            attributes,
            ..
        } = production
        else {
            continue;
        };
        if attributes.get("cell").is_none() || !cells.contains(sort) {
            continue;
        }
        for item in items {
            let ProductionItem::NonTerminal { sort, .. } = item else {
                continue;
            };
            if cells.contains(sort) {
                children.insert(sort.clone());
            } else if collections.contains(sort) {
                children.extend(
                    cells
                        .iter()
                        .filter(|cell| subsorts.directly_less_than(cell, sort))
                        .cloned(),
                );
            }
        }
    }
    let roots = cells.difference(&children).cloned().collect::<Vec<_>>();
    match roots.as_slice() {
        [root] => Ok(root.clone()),
        [] => Err("No root cell found".into()),
        _ => Err(format!(
            "Too many top cells for module {}: {}",
            definition.module(module).name,
            roots
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

fn counter_configuration(initial_fresh: usize) -> Sentence {
    configuration(counter_config_term(initial_fresh))
}

fn counter_config_term(initial_fresh: usize) -> Term {
    let name = cell_name_token("generatedCounter");
    Term::apply(
        "#configCell",
        vec![
            name.clone(),
            Term::apply("#cellPropertyListTerminator", Vec::new()),
            Term::Token {
                token: initial_fresh.to_string(),
                sort: Sort::new("Int"),
            },
            name,
        ],
    )
}

fn configuration(body: Term) -> Sentence {
    Sentence::Configuration {
        body,
        ensures: truth(),
        attributes: Attributes::default(),
    }
}

fn counter_helpers() -> [Sentence; 2] {
    let cell = Term::Variable {
        name: "Cell".into(),
        sort: Some(Sort::new(GENERATED_COUNTER_SORT)),
    };
    [
        Sentence::Production {
            label: Some(Label::new("getGeneratedCounterCell")),
            parameters: Vec::new(),
            sort: Sort::new(GENERATED_COUNTER_SORT),
            items: vec![
                ProductionItem::Terminal("getGeneratedCounterCell".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("GeneratedTopCell"),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes: attributes(&[("function", json!(""))]),
        },
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply(
                    "getGeneratedCounterCell",
                    vec![incomplete_cell(
                        GENERATED_TOP_CELL,
                        true,
                        cell.clone(),
                        true,
                    )],
                )),
                right: Box::new(cell),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        },
    ]
}

fn incomplete_cell(label: &str, open_left: bool, body: Term, open_right: bool) -> Term {
    Term::apply(
        label,
        vec![
            Term::apply(if open_left { "#dots" } else { "#noDots" }, Vec::new()),
            body,
            Term::apply(if open_right { "#dots" } else { "#noDots" }, Vec::new()),
        ],
    )
}

fn fresh_counter() -> Term {
    Term::Variable {
        name: "#Fresh".into(),
        sort: Some(Sort::new("Int")),
    }
}

fn cell_name_token(name: &str) -> Term {
    Term::Token {
        token: name.into(),
        sort: Sort::new("#CellName"),
    }
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn attributes(entries: &[(&str, serde_json::Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect(),
    )
}

fn rule_body(sentence: &Sentence) -> &Term {
    match sentence {
        Sentence::Rule { body, .. } => body,
        _ => unreachable!(),
    }
}

fn rewrite_left(term: &Term) -> Term {
    let metadata = term.metadata().cloned();
    let rebuilt = match term.unannotated() {
        Term::Rewrite { left, .. } => return rewrite_left(left),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(rewrite_left).collect(),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(rewrite_left).collect()),
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rewrite_left(pattern)),
            alias: alias.clone(),
        },
        _ => term.unannotated().clone(),
    };
    with_metadata(rebuilt, metadata)
}

trait TermApply {
    fn as_apply(&self) -> Option<(&Label, &[Term])>;
}

impl TermApply for Term {
    fn as_apply(&self) -> Option<(&Label, &[Term])> {
        match self.unannotated() {
            Term::Apply { label, arguments } => Some((label, arguments)),
            _ => None,
        }
    }
}

fn both_generated_top_productions(source: &Sentence, target: &Sentence) -> bool {
    matches!(
        (source, target),
        (
            Sentence::Production { label: Some(source), .. },
            Sentence::Production { label: Some(target), .. }
        ) if source.name == GENERATED_TOP_CELL && target.name == GENERATED_TOP_CELL
    )
}

fn with_metadata(term: Term, metadata: Option<crate::kast::TermMetadata>) -> Term {
    match metadata {
        Some(metadata) => term.with_metadata(metadata),
        None => term,
    }
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidFreshConstant,
        message: message.into(),
        source: None,
        location: None,
    }
}

fn error_from(message: String) -> ResolveFreshConstantsError {
    ResolveFreshConstantsError {
        diagnostics: vec![plain_error(message)],
    }
}
