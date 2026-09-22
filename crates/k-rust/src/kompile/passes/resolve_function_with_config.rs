//! This D12 transformation pass resolves required views, transforms sentences and terms, records origins, and rebases metadata when needed.
//! Its named `--timings` phase measures total cost; kompile counters measure resolution, rebasing, and transformed sentences.
//!
//! Thread the generated top-cell configuration through functions that inspect configuration.

use std::{
    collections::{BTreeMap, BTreeSet},
    convert::Infallible,
    fmt,
    sync::Arc,
};

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, LabelHead, ProductionCatalog, ProductionItem, ResolvedDefinition,
        Sentence, SortHead, production_identity,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{GeneratedCell, InternalLabel, Label, ProductionIdentity, Sort, Term},
    provenance::GeneratingPass,
};

use super::super::label_graph::LabelDependencyGraph;
use super::retarget_production_identities;

const CONFIGURATION_VARIABLE: &str = "#Configuration";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveFunctionWithConfigError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveFunctionWithConfigError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "function configuration resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveFunctionWithConfigError {}

/// Apply Java's `ResolveFunctionWithConfig.moduleResolve` transformation.
///
/// Functions whose rules inspect configuration receive one final `GeneratedTopCell` argument.
/// The requirement propagates backwards through calls to functions and non-macro `anywhere`
/// symbols, so callers receive and forward the same configuration value transitively.
pub fn resolve_function_with_config(
    definition: &Definition,
) -> Result<Definition, ResolveFunctionWithConfigError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_function_with_config_pass,
        Some(GeneratingPass::ResolveFunctionWithConfig),
    )
}

pub(crate) fn resolve_function_with_config_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveFunctionWithConfigError> {
    let resolved = input
        .resolved_raw()
        .map_err(|error| ResolveFunctionWithConfigError {
            diagnostics: vec![plain_error(error.to_string())],
        })?;
    let main_module = resolved
        .module_id(&input.definition.main_module)
        .expect("resolved definition contains its main module");
    let with_config = compute_with_config_functions(&resolved, main_module);
    if with_config.is_empty() {
        return Ok(input.definition.clone());
    }

    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();
    let mut replacements = BTreeMap::<ProductionIdentity, ProductionIdentity>::new();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        let top_sort_defined = resolved
            .sort_catalog(module_id)
            .defined_heads()
            .contains(&SortHead::new(BuiltinSort::GeneratedTopCell.k_name(), 0));
        let mut changed_production = false;
        let mut sentences = Vec::with_capacity(module.local_sentences.len() + 1);

        for sentence in &module.local_sentences {
            let transformed = match &**sentence {
                Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    attributes,
                } => Sentence::Rule {
                    body: transform_term(
                        resolve_with_config_body(
                            body.clone(),
                            &productions,
                            attributes,
                            &mut diagnostics,
                        ),
                        &with_config,
                    ),
                    requires: transform_term(requires.clone(), &with_config),
                    ensures: transform_term(ensures.clone(), &with_config),
                    attributes: attributes.clone(),
                },
                Sentence::Claim {
                    body,
                    requires,
                    ensures,
                    attributes,
                } => Sentence::Claim {
                    body: transform_term(
                        resolve_with_config_body(
                            body.clone(),
                            &productions,
                            attributes,
                            &mut diagnostics,
                        ),
                        &with_config,
                    ),
                    requires: transform_term(requires.clone(), &with_config),
                    ensures: transform_term(ensures.clone(), &with_config),
                    attributes: attributes.clone(),
                },
                Sentence::Context {
                    body,
                    requires,
                    attributes,
                } => Sentence::Context {
                    body: transform_term(body.clone(), &with_config),
                    requires: transform_term(requires.clone(), &with_config),
                    attributes: attributes.clone(),
                },
                Sentence::ContextAlias {
                    body,
                    requires,
                    attributes,
                } => Sentence::ContextAlias {
                    body: transform_term(body.clone(), &with_config),
                    requires: transform_term(requires.clone(), &with_config),
                    attributes: attributes.clone(),
                },
                Sentence::Production {
                    label: Some(label),
                    parameters,
                    sort,
                    items,
                    attributes,
                } if with_config.contains(&LabelHead::from(label)) => {
                    changed_production = true;
                    let mut items = items.clone();
                    if !matches!(
                        items.last(),
                        Some(ProductionItem::NonTerminal { sort, .. })
                            if sort.is_builtin(BuiltinSort::GeneratedTopCell)
                    ) {
                        items.push(ProductionItem::NonTerminal {
                            sort: Sort::builtin(BuiltinSort::GeneratedTopCell),
                            name: None,
                        });
                    }
                    Sentence::Production {
                        label: Some(label.clone()),
                        parameters: parameters.clone(),
                        sort: sort.clone(),
                        items,
                        attributes: attributes.clone(),
                    }
                }
                _ => (**sentence).clone(),
            };
            if let (Some(before), Some(after)) = (
                production_identity(sentence),
                production_identity(&transformed),
            ) && before != after
            {
                replacements.insert(before, after);
            }
            // Invariant: prior outer items and prior candidates for this item have been examined in order; the remaining inner iterator shrinks, giving O(n^2) over the two scanned collections.
            if !sentences.contains(&transformed) {
                sentences.push(transformed);
            }
        }
        if changed_production && !top_sort_defined {
            sentences.push(Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::GeneratedTopCell),
                attributes: Attributes::default(),
            });
        }
        module.local_sentences = sentences.into_iter().map(Arc::new).collect();
    }

    if !diagnostics.is_empty() {
        diagnostics.sort();
        diagnostics.dedup();
        return Err(ResolveFunctionWithConfigError { diagnostics });
    }

    retarget_production_identities(&mut output, &replacements);
    Ok(output)
}

/// Apply Java's later `resolveConfigVar` sentence transformation.
///
/// This remains a separate operation because the KORE pipeline deliberately runs it only after
/// cell concretization and semantics-module generation.
pub fn resolve_config_var(definition: &Definition) -> Definition {
    super::super::pipeline::run_standalone(
        definition,
        resolve_config_var_pass,
        Some(GeneratingPass::ResolveFunctionWithConfig),
    )
    .unwrap_or_else(|error| match error {})
}

pub(crate) fn resolve_config_var_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, Infallible> {
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            let sentence = crate::definition::sentence_mut(sentence);
            let (body, requires, ensures) = match sentence {
                Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    ..
                }
                | Sentence::Claim {
                    body,
                    requires,
                    ensures,
                    ..
                } => (body, requires, ensures),
                _ => continue,
            };
            if contains_rewrite(body)
                && [body as &Term, requires as &Term, ensures as &Term]
                    .into_iter()
                    .any(contains_exact_configuration_variable)
            {
                let left = rewrite_left(body);
                if matches!(
                    left.unannotated(),
                    Term::Apply { label, .. } if label.name == GeneratedCell::Top.label()
                ) {
                    let right = rewrite_right(body);
                    *body = Term::Rewrite {
                        left: Box::new(Term::As {
                            pattern: Box::new(left),
                            alias: Box::new(configuration_variable()),
                        }),
                        right: Box::new(right),
                    };
                }
            }
        }
    }
    Ok(output)
}

fn compute_with_config_functions(
    definition: &ResolvedDefinition,
    module: crate::definition::ModuleId,
) -> BTreeSet<LabelHead> {
    let productions = definition.production_catalog(module);
    let rules = definition.rule_catalog(module);
    let graph = LabelDependencyGraph::build(&productions, &rules, |rule| {
        rule.attributes().has_any(&AttributeKey::MACRO_LIKE)
    });
    let functions = productions.function_labels();
    let seeds = rules
        .rules()
        .filter_map(|(_, rule)| {
            let label = LabelHead::from(&crate::definition::match_rule_label(rule));
            (functions.contains(&label) && rule_needs_config(rule)).then_some(label)
        })
        .collect();
    graph.backward_closure(seeds)
}

fn rule_needs_config(rule: &Sentence) -> bool {
    let Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    } = rule
    else {
        return false;
    };
    if matches!(
        body.unannotated(),
        Term::Apply { label, .. } if label.is(InternalLabel::WithConfig)
    ) {
        return true;
    }
    contains_config_after_rewrites(body)
        || contains_configuration_need(requires)
        || contains_configuration_need(ensures)
}

fn contains_config_after_rewrites(term: &Term) -> bool {
    contains_configuration_need(&rewrite_right(term))
}

fn contains_configuration_need(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term.unannotated()
            && (name.starts_with('!') || name == CONFIGURATION_VARIABLE)
        {
            found = true;
        }
    });
    found
}

fn contains_exact_configuration_variable(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term.unannotated()
            && name == CONFIGURATION_VARIABLE
        {
            found = true;
        }
    });
    found
}

fn resolve_with_config_body(
    body: Term,
    productions: &ProductionCatalog<'_>,
    attributes: &Attributes,
    diagnostics: &mut Vec<Diagnostic>,
) -> Term {
    let Term::Apply { label, arguments } = body.unannotated() else {
        return body;
    };
    if !label.is(InternalLabel::WithConfig) {
        return body;
    }
    let [function, cell] = arguments.as_slice() else {
        diagnostics.push(error_at(
            format!(
                "#withConfig expects 2 arguments but received {}",
                arguments.len()
            ),
            attributes,
        ));
        return body;
    };

    let (function, right) = match function.unannotated() {
        Term::Rewrite { left, right } => ((**left).clone(), Some((**right).clone())),
        _ => (function.clone(), None),
    };
    let Term::Apply {
        label: function_label,
        arguments: function_arguments,
    } = function.unannotated()
    else {
        diagnostics.push(error_at(
            "Found term that is not a cell or a function at the top of a rule.",
            attributes,
        ));
        return body;
    };
    if productions
        .attributes_for(&LabelHead::from(function_label))
        .is_none_or(|attributes| !attributes.has(AttributeKey::Function))
    {
        diagnostics.push(error_at(
            "Found term that is not a cell or a function at the top of a rule.",
            attributes,
        ));
        return body;
    }
    let Term::Apply {
        label: cell_label, ..
    } = cell.unannotated()
    else {
        diagnostics.push(error_at(
            "Found term that is not a cell in the context of a function rule.",
            attributes,
        ));
        return body;
    };

    let configuration = if cell_label.name == GeneratedCell::Top.label() {
        cell.clone()
    } else {
        Term::Apply {
            label: Label::new(GeneratedCell::Top.label()),
            arguments: vec![
                Term::apply(InternalLabel::Dots.as_str(), vec![]),
                cell.clone(),
                Term::apply(InternalLabel::Dots.as_str(), vec![]),
            ],
        }
    };
    let mut new_arguments = function_arguments.clone();
    new_arguments.push(Term::As {
        pattern: Box::new(configuration),
        alias: Box::new(configuration_variable()),
    });
    let mut result = Term::Apply {
        label: function_label.clone(),
        arguments: new_arguments,
    };
    if let Some(metadata) = function.metadata() {
        result = result.with_metadata(metadata.clone());
    }
    if let Some(right) = right {
        Term::Rewrite {
            left: Box::new(result),
            right: Box::new(right),
        }
    } else {
        result
    }
}

// Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
fn transform_term(term: Term, with_config: &BTreeSet<LabelHead>) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            transform_term(*term, with_config).with_metadata(metadata)
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform_term(*left, with_config)),
            right: Box::new(transform_term(*right, with_config)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(transform_term(*pattern, with_config)),
            alias: Box::new(transform_term(*alias, with_config)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform_term(item, with_config))
                .collect(),
        ),
        Term::Apply {
            label,
            mut arguments,
        } => {
            let already_resolved = arguments.last().is_some_and(is_configuration_argument);
            arguments = arguments
                .into_iter()
                .map(|argument| transform_term(argument, with_config))
                .collect();
            if with_config.contains(&LabelHead::from(&label)) && !already_resolved {
                arguments.push(configuration_variable());
            }
            Term::Apply { label, arguments }
        }
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
    }
}

fn is_configuration_argument(term: &Term) -> bool {
    match term.unannotated() {
        Term::Variable { name, .. } => name == CONFIGURATION_VARIABLE,
        Term::As { alias, .. } => matches!(
            alias.unannotated(),
            Term::Variable { name, .. } if name == CONFIGURATION_VARIABLE
        ),
        _ => false,
    }
}

fn configuration_variable() -> Term {
    Term::Variable {
        name: CONFIGURATION_VARIABLE.to_owned(),
        sort: Some(Sort::builtin(BuiltinSort::GeneratedTopCell)),
    }
}

fn contains_rewrite(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        if matches!(term.unannotated(), Term::Rewrite { .. }) {
            found = true;
        }
    });
    found
}

fn rewrite_left(term: &Term) -> Term {
    match term.unannotated() {
        Term::Rewrite { left, .. } => rewrite_left(left),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(rewrite_left).collect(),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(rewrite_left).collect()),
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rewrite_left(pattern)),
            alias: alias.clone(),
        },
        term => term.clone(),
    }
}

fn rewrite_right(term: &Term) -> Term {
    match term.unannotated() {
        Term::Rewrite { right, .. } => rewrite_right(right),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(rewrite_right).collect(),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(rewrite_right).collect()),
        Term::As { alias, .. } => (**alias).clone(),
        term => term.clone(),
    }
}

fn error_at(message: impl Into<String>, attributes: &Attributes) -> Diagnostic {
    Diagnostic::error_at(
        DiagnosticCode::InvalidFunctionConfiguration,
        message,
        attributes,
    )
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidFunctionConfiguration,
        message: message.into(),
        source: None,
        location: None,
    }
}
