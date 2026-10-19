//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Thread the generated top-cell configuration through functions that inspect configuration.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    collections::{BTreeMap, BTreeSet},
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
    kast::{GeneratedCell, InternalLabel, Label, ProductionIdentity, Sort, Term, TermParts},
    provenance::GeneratingPass,
};

use super::super::label_graph::{Edges, LabelDependencyGraph};
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

/// Functions whose rules inspect configuration receive one final `GeneratedTopCell` argument.
/// A function reads the configuration when its own rules do, or when a function or macro that its
/// rules reach does: the requirement propagates backwards along every application in the body,
/// `requires` and `ensures` of a function rule, and through a macro to what its right side
/// applies, since expansion puts that right side where the macro is used. A rule counts for the
/// label its head has once macros are expanded, so a simplification rule written with a macro or
/// alias head is a rule of the function that head expands to. The set is the least
/// fixed point of that relation, so a function that calls a configuration-reading function
/// receives and forwards the same configuration value transitively. Only function labels receive
/// it: a macro is a route only, and an `anywhere` symbol that is not a function is a call target
/// only, whose own rules give the closure no edges.
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
    let with_config = compute_with_config_functions(resolved, main_module);
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
        let mut sentences = Vec::<Sentence>::with_capacity(module.local_sentences.len() + 1);

        // Invariant: `sentences` holds, without duplicates, the transformed form of every sentence of `module.local_sentences` before `sentence`, `replacements` their changed production identities, and `changed_production` whether one of them was a production in `with_config`; each iteration consumes one sentence, and the `sentences` equality scan makes the loop quadratic in the module's sentence count.
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
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => (**sentence).clone(),
            };
            if let (Some(before), Some(after)) = (
                production_identity(sentence),
                production_identity(&transformed),
            ) && before != after
            {
                replacements.insert(before, after);
            }
            match sentences
                .iter()
                .position(|existing| *existing == transformed)
            {
                // Equal sentences become one, which derives from both inputs.
                Some(index) => sentences[index]
                    .attributes_mut()
                    .union_input_addresses(transformed.attributes()),
                None => sentences.push(transformed),
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

/// Bind the configuration variable in the rules and claims that mention it: a rewrite whose
/// left-hand side is the generated top cell gets that cell aliased (`#as`) to the variable.
///
/// This is a separate operation from [`resolve_function_with_config`] because the left-hand side
/// is the generated top cell only after cell concretization; the KORE pipeline runs it after
/// cell concretization and semantics-module generation, and so after macro expansion.
///
/// After binding, a rule or claim that still holds the variable where the root of its left-hand
/// side does not bind it ([`left_hand_side_binds_configuration`], the predicate of invariant CF1)
/// has no configuration in scope, and is rejected at the sentence
/// ([`DiagnosticCode::InvalidFunctionConfiguration`]). Reading the configuration needs one in
/// scope: a rewrite of the configuration has it (its left-hand side is the generated top cell, which
/// this stage aliases), and so has a rule of a function that receives it as its last argument. An
/// anywhere rule whose head is not a function holds wherever its left-hand side occurs, also outside
/// any configuration, and such a head never receives the configuration, since only the rules of
/// functions propagate the need for it ([`resolve_function_with_config`]); an equational claim states
/// the value of its left-hand side, a term. A macro-like rule is exempt: its expansion substitutes
/// the reference into a use site, which binds it.
///
/// A rule whose head is a function is not rejected here: its function has the configuration in
/// scope by meaning, since [`resolve_function_with_config`] gives the configuration to every
/// function whose rules reach a read, through `requires`, `ensures`, right-hand sides and macros.
/// An unbound reference in such a rule would be a read that propagation missed, a compiler defect
/// that CF1 reports in invariant builds.
pub fn resolve_config_var(
    definition: &Definition,
) -> Result<Definition, ResolveFunctionWithConfigError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_config_var_pass,
        Some(GeneratingPass::ResolveFunctionWithConfig),
    )
}

pub(crate) fn resolve_config_var_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveFunctionWithConfigError> {
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            // Only rules and claims change. The kind is decided before taking a mutable sentence,
            // which copies a shared one, so every other kind stays shared.
            match &**sentence {
                Sentence::Rule { .. } | Sentence::Claim { .. } => {}
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => continue,
            }
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
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => {
                    unreachable!("copy-on-write keeps the kind decided above")
                }
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
    let mut diagnostics = Vec::new();
    for module in &output.modules {
        // Invariant: `diagnostics` holds the rejection of every sentence of `module` before
        // `sentence` that reads the configuration with none in scope.
        for sentence in &module.local_sentences {
            let Some(read) = unscoped_configuration_read(sentence) else {
                continue;
            };
            // The function heads are looked up only for such a sentence, which is rare.
            let resolved =
                input
                    .resolved_raw()
                    .map_err(|error| ResolveFunctionWithConfigError {
                        diagnostics: vec![plain_error(error.to_string())],
                    })?;
            let function_rule = matches!(&**sentence, Sentence::Rule { .. })
                && resolved.module_id(&module.name).is_some_and(|module| {
                    resolved
                        .production_catalog(module)
                        .function_labels()
                        .contains(&LabelHead::from(&crate::definition::match_rule_label(
                            sentence,
                        )))
                });
            if function_rule {
                continue;
            }
            diagnostics.push(read);
        }
    }
    if !diagnostics.is_empty() {
        diagnostics.sort();
        diagnostics.dedup();
        return Err(ResolveFunctionWithConfigError { diagnostics });
    }
    Ok(output)
}

/// Whether the root of the left-hand side of `body` (the left side of its top rewrite, or `body`
/// without one) binds the configuration variable: it is the generated top cell aliased to it
/// (`<generatedTop>(..) #as #Configuration`), or an application whose last argument is the
/// variable or that alias, the left-hand side of a rule of a function that receives the
/// configuration. This is the one predicate of the binding stage's rejection and of invariant CF1;
/// CF1 also checks, through [`configuration_binder`], that the root of the second form is a function
/// that receives the configuration.
pub(crate) fn left_hand_side_binds_configuration(body: &Term) -> bool {
    configuration_binder(body).is_some()
}

/// How the root of the left-hand side of `body` binds the configuration variable
/// ([`left_hand_side_binds_configuration`]).
pub(crate) enum ConfigurationBinder<'a> {
    /// The generated top cell aliased to it.
    TopCellAlias,
    /// The last argument of the root application, whose label this is.
    LastArgument(
        #[cfg_attr(
            not(any(debug_assertions, feature = "kompile-invariant-checks")),
            expect(
                dead_code,
                reason = "only invariant CF1, absent from this build, reads the label"
            )
        )]
        &'a Label,
    ),
}

/// The binder of the configuration variable at the root of the left-hand side of `body`, if any.
pub(crate) fn configuration_binder(body: &Term) -> Option<ConfigurationBinder<'_>> {
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only a top rewrite has a left side other than the body"
    )]
    let left = match body.unannotated() {
        Term::Rewrite { left, .. } => left.as_ref(),
        _ => body,
    };
    if is_configuration_alias(left) {
        return Some(ConfigurationBinder::TopCellAlias);
    }
    if let Term::Apply { label, arguments } = left.unannotated()
        && arguments.last().is_some_and(|last| {
            is_exact_configuration_variable(last) || is_configuration_alias(last)
        })
    {
        return Some(ConfigurationBinder::LastArgument(label));
    }
    None
}

/// Whether `term` is the configuration variable. Reading the spelling is sound: a name that
/// starts with `#` is reserved for the compiler, so no authored variable has it.
pub(crate) fn is_exact_configuration_variable(term: &Term) -> bool {
    matches!(term.unannotated(), Term::Variable { name, .. } if name == CONFIGURATION_VARIABLE)
}

/// Whether `term` is the generated top cell aliased to the configuration variable.
fn is_configuration_alias(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::As { pattern, alias }
            if is_exact_configuration_variable(alias)
                && matches!(
                    pattern.unannotated(),
                    Term::Apply { label, .. } if label.name == GeneratedCell::Top.label()
                )
    )
}

/// The rejection of `sentence`, a bound rule or claim, when it is not macro-like and holds the
/// configuration variable where the root of its left-hand side does not bind it
/// ([`resolve_config_var`]); the caller exempts the rules of functions.
///
/// The variable reaches such a sentence as the last argument of a call to a function that
/// receives the configuration, directly or through a macro it uses, so the message names those
/// functions and the parts of the sentence that call them.
fn unscoped_configuration_read(sentence: &Sentence) -> Option<Diagnostic> {
    let (kind, body, requires, ensures, attributes) = match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } => ("rule", body, requires, ensures, attributes),
        Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } => ("claim", body, requires, ensures, attributes),
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => return None,
    };
    if attributes.has_any(&AttributeKey::MACRO_LIKE) || left_hand_side_binds_configuration(body) {
        return None;
    }
    let (left, right) = (rewrite_left(body), rewrite_right(body));
    let parts = [
        ("left-hand side", &left),
        ("requires clause", requires),
        ("ensures clause", ensures),
        ("right-hand side", &right),
    ]
    .into_iter()
    .filter(|(_, term)| contains_exact_configuration_variable(term))
    .collect::<Vec<_>>();
    if parts.is_empty() {
        return None;
    }
    let mut readers = BTreeSet::new();
    for (_, term) in &parts {
        term.visit_preorder(&mut |node| {
            if let Term::Apply { label, arguments } = node.unannotated()
                && arguments.last().is_some_and(is_configuration_argument)
            {
                readers.insert(label.name.clone());
            }
        });
    }
    let places = parts
        .iter()
        .map(|(place, _)| *place)
        .collect::<Vec<_>>()
        .join(" and ");
    let calls = if readers.is_empty() {
        "reads it".to_owned()
    } else {
        let readers = readers.into_iter().collect::<Vec<_>>();
        let (verb, relative) = match (parts.len(), readers.len()) {
            (1, 1) => ("calls", "reads"),
            (1, _) => ("calls", "read"),
            (_, 1) => ("call", "reads"),
            _ => ("call", "read"),
        };
        format!("{verb} {}, which {relative} it", readers.join(", "))
    };
    let (subject, scope) = if attributes.has(AttributeKey::Anywhere) {
        (
            "An anywhere rule",
            "it applies to its left-hand side wherever that term occurs, also outside any \
             configuration, and its head is not a function, which would receive the \
             configuration as an argument",
        )
    } else if kind == "claim" {
        (
            "A claim",
            "its left-hand side is neither the configuration nor an application of a function \
             that receives it",
        )
    } else {
        (
            "A rule",
            "its left-hand side is neither the configuration nor an application of a function \
             that receives it",
        )
    };
    Some(error_at(
        format!(
            "{subject} cannot read the configuration: its {places} {calls}, and the {kind} has no \
             configuration in scope: {scope}."
        ),
        attributes,
    ))
}

fn compute_with_config_functions(
    definition: &ResolvedDefinition,
    module: crate::definition::ModuleId,
) -> BTreeSet<LabelHead> {
    let productions = definition.production_catalog(module);
    let rules = definition.rule_catalog(module);
    let graph = LabelDependencyGraph::build(
        &productions,
        &rules,
        |rule| rule.attributes().has_any(&AttributeKey::MACRO_LIKE),
        Edges::READS,
    );
    let functions = productions.function_labels();
    // A rule is a seed for the labels it is a rule of once macros are expanded, so a
    // simplification rule written with a macro head seeds the function that head expands to.
    let seeds = rules
        .rules()
        .filter(|(_, rule)| rule_needs_config(rule))
        .flat_map(|(_, rule)| graph.rule_heads(rule))
        .filter(|label| functions.contains(label))
        .collect();
    // A macro label reaches the closure when a reader is reachable through its right side; it is
    // a route, not a receiver: its applications are expanded where they are used.
    graph
        .backward_closure(seeds)
        .into_iter()
        .filter(|label| functions.contains(label))
        .collect()
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

/// A function rule written with configuration context, `[[ F ]] C`, which loads as the rule
/// body `#withConfig(F, C)`.
///
/// `rule`, the first argument, is the function rule: an application of the function, or a
/// rewrite whose left side is one. `context`, the second, is the configuration context: a cell
/// fragment that the lowering places below the generated top cell and passes to the function as
/// its configuration argument. This is the one reading of the two argument roles, shared by the
/// lowering and the typing view.
pub(crate) struct FunctionRuleWithContext<'a> {
    pub(crate) rule: &'a Term,
    pub(crate) context: &'a Term,
}

impl<'a> FunctionRuleWithContext<'a> {
    /// `None` when `body` is not a `#withConfig` application; `Some(Err(arity))` when it is one
    /// with other than two arguments.
    pub(crate) fn of(body: &'a Term) -> Option<Result<Self, usize>> {
        let Term::Apply { label, arguments } = body.unannotated() else {
            return None;
        };
        if !label.is(InternalLabel::WithConfig) {
            return None;
        }
        Some(match arguments.as_slice() {
            [rule, context] => Ok(Self { rule, context }),
            _ => Err(arguments.len()),
        })
    }
}

fn resolve_with_config_body(
    body: Term,
    productions: &ProductionCatalog<'_>,
    attributes: &Attributes,
    diagnostics: &mut Vec<Diagnostic>,
) -> Term {
    let (function, cell) = match FunctionRuleWithContext::of(&body) {
        None => return body,
        Some(Err(arity)) => {
            diagnostics.push(error_at(
                format!("#withConfig expects 2 arguments but received {arity}"),
                attributes,
            ));
            return body;
        }
        Some(Ok(FunctionRuleWithContext { rule, context })) => (rule, context),
    };

    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
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

// Invariant: each call rebuilds `term` from its transformed immediate subterms and appends the configuration variable to an application whose label is in `with_config` and whose last argument is not already a configuration argument; the finite `term` bounds the recursion.
fn transform_term(term: Term, with_config: &BTreeSet<LabelHead>) -> Term {
    match term.into_parts() {
        TermParts::Annotated { term, metadata } => {
            transform_term(*term, with_config).with_metadata(metadata)
        }
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform_term(*left, with_config)),
            right: Box::new(transform_term(*right, with_config)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(transform_term(*pattern, with_config)),
            alias: Box::new(transform_term(*alias, with_config)),
        },
        TermParts::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform_term(item, with_config))
                .collect(),
        ),
        TermParts::Apply {
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
        leaf @ (TermParts::InjectedLabel(_)
        | TermParts::Variable { .. }
        | TermParts::Token { .. }) => Term::from(leaf),
    }
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
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

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
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

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
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
        input_addresses: Vec::new(),
    }
}

/// The stage on the definition the pipeline gives it ([`crate::kompile::stage_harness`]).
#[cfg(test)]
mod stage_tests {
    use crate::{
        definition::{ProductionItem, Sentence},
        kompile::stage_harness::{module, run_to_stage},
    };

    /// A function equation is applied without the configuration, so a function whose value
    /// depends on it (an equation written `[[ f() => V ]] <s> V </s>`) receives the whole
    /// configuration as an extra argument, and so must every function whose equations call
    /// it, directly or through others: the backward closure of the configuration readers over
    /// the call graph. The functions the pipeline hands this stage include the ones lifted
    /// from local functions, so a lifted `#fun` that calls a reader is in the closure too,
    /// and a function that reaches no reader keeps its arity.
    #[test]
    fn every_function_that_can_reach_a_configuration_reader_receives_the_configuration() {
        let run = run_to_stage(
            r#"
module MAIN
  syntax K
  syntax Int ::= r"[0-9]+" [token]
  syntax Int ::= reader() [function, symbol(reader)]
               | caller() [function, symbol(caller)]
               | plain() [function, symbol(plain)]
  syntax KItem ::= "go" [symbol(go)] | done(Int) [symbol(done)]
  configuration <t> <k> go </k> <s> 0 </s> </t>
  rule [[ reader() => V ]] <s> V </s>
  rule caller() => reader()
  rule plain() => 1
  rule <k> go => done(#fun(X => caller())(plain())) </k> [label(go)]
endmodule
"#,
            "resolve function configuration",
        );
        let arguments = |definition, label: &str| {
            module(definition, "MAIN")
                .local_sentences
                .iter()
                .find_map(|sentence| {
                    let Sentence::Production {
                        label: Some(production),
                        items,
                        ..
                    } = &**sentence
                    else {
                        return None;
                    };
                    (production.name == label).then(|| {
                        items
                            .iter()
                            .filter_map(|item| match item {
                                ProductionItem::NonTerminal { sort, .. } => Some(sort.to_string()),
                                ProductionItem::Terminal(_)
                                | ProductionItem::RegexTerminal { .. } => None,
                            })
                            .collect::<Vec<_>>()
                    })
                })
                .unwrap_or_else(|| panic!("no production {label}"))
        };
        for (label, before, after) in [
            ("reader", &[][..], &["GeneratedTopCell"][..]),
            ("caller", &[], &["GeneratedTopCell"]),
            ("#lambda__", &["K"], &["K", "GeneratedTopCell"]),
            ("plain", &[], &[]),
        ] {
            assert_eq!(arguments(&run.input, label), before, "{label} before");
            assert_eq!(arguments(run.output(), label), after, "{label} after");
        }
    }

    /// The need for the configuration also propagates through a function rule's `ensures` and
    /// through macros: a function whose rule calls a macro whose right side calls a reader reads
    /// the configuration, as the rule does once the macro is expanded. Only functions receive it:
    /// the macro and the constructor in its right side keep their arity.
    #[test]
    fn the_configuration_reaches_a_function_through_its_ensures_and_through_macros() {
        let run = run_to_stage(
            r#"
module MAIN
  syntax K
  syntax Int ::= r"[0-9]+" [token]
  syntax Bool ::= "tt" [token]
  syntax Int ::= reader() [function, symbol(reader)]
               | viaEnsures() [function, symbol(viaEnsures)]
  syntax Box ::= readerM() [macro, symbol(readerM)]
               | viaMacro() [function, symbol(viaMacro)]
               | wrap(Int) [symbol(wrap)]
  syntax Bool ::= flag() [function, symbol(flag)]
  syntax KItem ::= "go" [symbol(go)] | done(Box) [symbol(done)]
  configuration <t> <k> go </k> <s> 0 </s> <b> tt </b> </t>
  rule [[ reader() => V ]] <s> V </s>
  rule [[ flag() => B ]] <b> B </b>
  rule readerM() => wrap(reader())
  rule viaMacro() => readerM()
  rule viaEnsures() => 1 ensures flag()
  rule <k> go => done(viaMacro()) </k> [label(go)]
endmodule
"#,
            "resolve function configuration",
        );
        let arity = |label: &str| {
            module(run.output(), "MAIN")
                .local_sentences
                .iter()
                .find_map(|sentence| {
                    let Sentence::Production {
                        label: Some(production),
                        items,
                        ..
                    } = &**sentence
                    else {
                        return None;
                    };
                    (production.name == label).then(|| {
                        items
                            .iter()
                            .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
                            .count()
                    })
                })
                .unwrap_or_else(|| panic!("no production {label}"))
        };
        for (label, expected) in [
            ("reader", 1),
            ("flag", 1),
            ("viaMacro", 1),
            ("viaEnsures", 1),
            ("readerM", 0),
            ("wrap", 1),
        ] {
            assert_eq!(arity(label), expected, "{label}");
        }
    }
}
