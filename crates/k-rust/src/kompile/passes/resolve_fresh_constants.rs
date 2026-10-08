//! ```toml algorithm
//! id = "kompile.fresh_constants.resolve"
//! name = "resolution of fresh constants"
//! sites = ["resolve_fresh_constants", "resolve_fresh_constants_pass", "fresh_variables", "transform_term"]
//! variable = "N = traversed terms; F = fresh variables; L = local sentences; P = productions visible in one module"
//! counters = []
//! no_counter = "fresh-constant resolution has no dedicated counter; its sites bump KompileSentenceCopies and KompileProductionIdentityDigests, and the configuration expansion and retargeting it runs bump ProvenanceSetNodesBuilt, KompileResolveCalls and KompileResolveUpdates"
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(N + F log F + L) plus one definition.catalog.sort construction for the main module, one definition.configuration.expand run, one kompile.metadata.retarget run, and per module one production catalog and O(P log P) scans of it"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Each module scans its visible productions a constant number of times: for its fresh generators, its generated top cell, and, once when the module has a claim, its cell labels (`cell_labels_of`).
//! A claim that mentions a configuration cell and not the counter gets `<generatedCounter> _GenN => ?_GenM </generatedCounter>`.
//! The counter cell exists only when the main module's sort catalog (built once) admits `Int` domain values.
//!
//! Resolve fresh rule variables through per-sort generators and a counter cell.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{collections::BTreeMap, collections::BTreeSet, fmt, sync::Arc};

use serde_json::json;

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, LabelHead, ProductionCatalog, ProductionItem, ResolvedDefinition,
        Sentence, expand_configurations_allowing_reserved_cells, production_identity,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{
        FrontendSort, GeneratedCell, InternalLabel, Label, ProductionIdentity, Sort, Term,
        TermParts, WellKnownModule,
    },
    provenance::GeneratingPass,
};

use super::retarget_production_identities;

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

/// Resolve fresh rule variables through per-sort generators and a counter cell.
pub fn resolve_fresh_constants(
    definition: &Definition,
    initial_fresh: usize,
) -> Result<Definition, ResolveFreshConstantsError> {
    super::super::pipeline::run_standalone(
        definition,
        |input, state| {
            state.fresh_config_count = Some(initial_fresh);
            resolve_fresh_constants_pass(input, state)
        },
        Some(GeneratingPass::ResolveFreshConstants),
    )
}

pub(crate) fn resolve_fresh_constants_pass(
    input: &super::super::pipeline::PassInput<'_>,
    state: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveFreshConstantsError> {
    let initial_fresh = state
        .fresh_config_count
        .expect("`Artifacts::FRESH_CONFIG_COUNT` is provided before this pass runs");
    let resolved = input
        .resolved_raw()
        .map_err(|error| error_from(error.to_string()))?;
    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();
    let mut replacements = BTreeMap::<ProductionIdentity, ProductionIdentity>::new();
    // The counter cell holds an `Int` (initially the domain value `0`), so the configuration
    // has one only when the main module, whose view is the emitted definition and whose
    // configuration is executed, sees an `Int` with domain values. Without one no rule can
    // draw from a counter (a generator takes an `Int`), and declaring the cell would name an
    // undeclared sort.
    // Domain values come from the token declarations among the visible sentences, so the
    // catalog of those sentences alone decides it, without the imported modules' catalogs.
    let counter_cell =
        crate::definition::SortCatalog::from_visible(resolved.sentences(resolved.main_module_id()))
            .admits_domain_value(&Sort::builtin(BuiltinSort::Int));

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
            .any(|label| label.as_str() == GeneratedCell::Top.label());
        let local_generated_top = productions
            .local_labels()
            .contains(&LabelHead::new(GeneratedCell::Top.label()));

        let cell_labels = std::cell::OnceCell::new();
        // The first sentence of the module whose lowering advances the counter, which the
        // module's `INT` import is for; it locates the error when the definition has no `INT`
        // or no counter cell.
        let mut first_counter_use = None;
        for sentence in &mut module.local_sentences {
            let sentence = crate::definition::sentence_mut(sentence);
            let before_identity = production_identity(sentence);
            let original = sentence.clone();
            match transform_sentence(
                original,
                &productions,
                &generators,
                &cell_labels,
                counter_cell,
            ) {
                Ok((transformed, counter)) => {
                    if let (Some(before), Some(after)) =
                        (before_identity, production_identity(&transformed))
                        && before != after
                    {
                        replacements.insert(before, after);
                    }
                    if counter == CounterUse::Advances && first_counter_use.is_none() {
                        first_counter_use = Some(transformed.clone());
                    }
                    *sentence = transformed;
                }
                Err(message) => diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidFreshConstant,
                    message,
                    sentence,
                )),
            }
        }
        // The counter cell is an `Int` advanced with `_+Int_`, which the rule's module declares
        // only when it sees `INT`; the user's rule means the same without that import. Without
        // `INT` that is the report; with it, a definition without the counter cell has nowhere
        // to draw the value from.
        if let Some(first_use) = first_counter_use {
            if !super::import_for_generated(module, resolved, WellKnownModule::Int) {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidFreshConstant,
                    super::missing_module_message(
                        "A fresh variable",
                        "an increment of the fresh counter",
                        WellKnownModule::Int,
                    ),
                    &first_use,
                ));
            } else if !counter_cell {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidFreshConstant,
                    format!(
                        "A fresh variable draws its value from the fresh counter cell, which holds an Int starting at the domain value 0, but the main module {} sees no sort Int with domain values, so the configuration has no counter cell.",
                        input.definition.main_module
                    ),
                    &first_use,
                ));
            }
        }

        let has_cells = productions
            .productions()
            .any(|(_, production)| production.attributes().has(AttributeKey::Cell));
        let counter = counter_cell.then_some(initial_fresh);
        let configuration =
            if module.name == input.definition.main_module && !visible_generated_top && has_cells {
                match generated_top_configuration(resolved, module_id, &productions, counter) {
                    Ok(configuration) => Some(configuration),
                    Err(message) => {
                        diagnostics.push(plain_error(message));
                        None
                    }
                }
            } else if local_generated_top {
                counter.map(counter_configuration)
            } else {
                None
            };
        if let Some(configuration) = configuration {
            if counter_cell {
                // Invariant: `module.local_sentences` contains each helper of `counter_helpers()` before `sentence`; each iteration consumes one of the two helpers and scans `module.local_sentences` once.
                for sentence in counter_helpers() {
                    if !module
                        .local_sentences
                        .iter()
                        .any(|candidate| **candidate == sentence)
                    {
                        module.local_sentences.push(Arc::new(sentence));
                    }
                }
            }
            module.local_sentences.push(Arc::new(configuration));
        }
        for sentence in &mut module.local_sentences {
            let sentence = crate::definition::sentence_mut(sentence);
            let before_identity = production_identity(sentence);
            fix_generated_top_format(sentence);
            if let (Some(before), Some(after)) = (before_identity, production_identity(sentence))
                && before != after
            {
                replacements.insert(before, after);
            }
        }
    }

    if !diagnostics.is_empty() {
        diagnostics.sort();
        diagnostics.dedup();
        return Err(ResolveFreshConstantsError { diagnostics });
    }

    let mut expanded = expand_configurations_allowing_reserved_cells(&output)
        .map_err(|error| error_from(error.to_string()))?;
    for module in &mut expanded.modules {
        for sentence in &mut module.local_sentences {
            let sentence = crate::definition::sentence_mut(sentence);
            let before_identity = production_identity(sentence);
            fix_generated_top_format(sentence);
            if let (Some(before), Some(after)) = (before_identity, production_identity(sentence))
                && before != after
            {
                replacements.insert(before, after);
            }
        }
    }
    retarget_production_identities(&mut expanded, &replacements);
    Ok(expanded)
}

/// Lower `sentence`'s fresh variables; `counter_cell` says whether the configuration has the
/// counter cell, which the generated top production, its initializer and claims then mention.
fn transform_sentence(
    sentence: Sentence,
    productions: &ProductionCatalog<'_>,
    generators: &BTreeMap<Sort, Label>,
    cell_labels: &std::cell::OnceCell<BTreeSet<String>>,
    counter_cell: bool,
) -> Result<(Sentence, CounterUse), String> {
    let mut counter = CounterUse::None;
    let transformed = transform_sentence_counting(
        sentence,
        productions,
        generators,
        cell_labels,
        counter_cell,
        &mut counter,
    )?;
    Ok((transformed, counter))
}

/// Whether the lowering of a sentence advances the counter cell (`add_fresh_cell`), whose
/// increment is `INT`'s `_+Int_`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CounterUse {
    None,
    Advances,
}

fn transform_sentence_counting(
    sentence: Sentence,
    productions: &ProductionCatalog<'_>,
    generators: &BTreeMap<Sort, Label>,
    cell_labels: &std::cell::OnceCell<BTreeSet<String>>,
    counter_cell: bool,
    counter: &mut CounterUse,
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
            if counter_cell
                && with_fresh.attributes().has(AttributeKey::Initializer)
                && rewrite_left(rule_body(&with_fresh))
                    .as_apply()
                    .is_some_and(|(label, _)| label.name == GeneratedCell::Top.initializer())
            {
                return add_counter_initializer(with_fresh);
            }
            if rule_defines_function(&original, productions) {
                // An equation has no counter cell to draw from; the definition checks reject a
                // fresh variable in it (`definition::checks::fresh_variables`).
                Ok(original)
            } else {
                if !fresh.is_empty() {
                    *counter = CounterUse::Advances;
                }
                Ok(with_fresh)
            }
        }
        Sentence::Context {
            body,
            requires,
            attributes,
        } => {
            let fresh = fresh_variables([&body, &requires]);
            if !fresh.is_empty() {
                *counter = CounterUse::Advances;
            }
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
        production @ Sentence::Production { .. } if counter_cell => {
            Ok(add_counter_to_top_production(production))
        }
        Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } => {
            // The counter cell is not part of the configuration a claim's author declares: this
            // pass adds it to give `!` variables their values and advances it in every rule that
            // uses one. A claim over the declared cells therefore says nothing about the counter
            // except that it has some value before and some value after the path, which is
            // `<generatedCounter> _GenN => ?_GenM </generatedCounter>`. Leaving the cell to the
            // configuration's frame would instead claim that no `!` variable is instantiated.
            // Without the counter cell there is no counter to say anything about.
            let cell_labels = cell_labels.get_or_init(|| cell_labels_of(productions));
            let body = if counter_cell
                && mentions_label(&body, |name| cell_labels.contains(name))
                && !mentions_label(&body, |name| name == GeneratedCell::Counter.label())
            {
                let mut names =
                    super::super::fresh_names::FreshNames::for_terms([&body, &requires, &ensures]);
                let before = names.mint("_Gen");
                let after = names.mint("?_Gen");
                add_claim_counter_cell(body, before, after)
            } else {
                body
            };
            Ok(Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            })
        }
        sentence @ Sentence::Production { .. }
        | sentence @ Sentence::SyntaxSort { .. }
        | sentence @ Sentence::SortSynonym { .. }
        | sentence @ Sentence::SyntaxLexical { .. }
        | sentence @ Sentence::SyntaxAssociativity { .. }
        | sentence @ Sentence::SyntaxPriority { .. }
        | sentence @ Sentence::ContextAlias { .. }
        | sentence @ Sentence::Configuration { .. }
        | sentence @ Sentence::Bubble { .. } => Ok(sentence),
    }
}

/// Labels of the cell productions visible in a module.
fn cell_labels_of(productions: &ProductionCatalog<'_>) -> BTreeSet<String> {
    productions
        .productions()
        .filter_map(|(_, production)| match production {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.has(AttributeKey::Cell) => Some(label.name.clone()),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
        })
        .collect()
}

fn mentions_label(body: &Term, mut matches: impl FnMut(&str) -> bool) -> bool {
    let mut found = false;
    body.visit_preorder(&mut |term| {
        if !found
            && let Term::Apply { label, .. } = term
            && matches(&label.name)
        {
            found = true;
        }
    });
    found
}

/// `#cells(body, <generatedCounter> before => after </generatedCounter>)` with `Int` variables.
fn add_claim_counter_cell(body: Term, before: String, after: String) -> Term {
    let variable = |name: String| Term::Variable {
        name,
        sort: Some(Sort::builtin(BuiltinSort::Int)),
    };
    Term::apply(
        InternalLabel::Cells.as_str(),
        vec![
            body,
            incomplete_cell(
                GeneratedCell::Counter.label(),
                false,
                Term::Rewrite {
                    left: Box::new(variable(before)),
                    right: Box::new(variable(after)),
                },
                false,
            ),
        ],
    )
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
    match term.into_unannotated().into_parts() {
        TermParts::Variable { name, sort } if fresh.contains_key(&name) => {
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
                            sort: Sort::builtin(BuiltinSort::Int),
                        },
                    ],
                )],
            })
        }
        TermParts::Apply { label, arguments } => Ok(with_metadata(
            Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| transform_term(argument, fresh, offsets, generators))
                    .collect::<Result<_, _>>()?,
            },
            metadata,
        )),
        TermParts::Rewrite { left, right } => Ok(with_metadata(
            Term::Rewrite {
                left: Box::new(transform_term(*left, fresh, offsets, generators)?),
                right: Box::new(transform_term(*right, fresh, offsets, generators)?),
            },
            metadata,
        )),
        TermParts::As { pattern, alias } => Ok(with_metadata(
            Term::As {
                pattern: Box::new(transform_term(*pattern, fresh, offsets, generators)?),
                alias: Box::new(transform_term(*alias, fresh, offsets, generators)?),
            },
            metadata,
        )),
        TermParts::Sequence(items) => Ok(with_metadata(
            Term::Sequence(
                items
                    .into_iter()
                    .map(|item| transform_term(item, fresh, offsets, generators))
                    .collect::<Result<_, _>>()?,
            ),
            metadata,
        )),
        leaf @ (TermParts::InjectedLabel(_)
        | TermParts::Variable { .. }
        | TermParts::Token { .. }) => Ok(with_metadata(Term::from(leaf), metadata)),
        TermParts::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    }
}

fn add_fresh_cell(body: Term, count: usize) -> Term {
    if count == 0 {
        return body;
    }
    Term::apply(
        InternalLabel::Cells.as_str(),
        vec![
            body,
            incomplete_cell(
                GeneratedCell::Counter.label(),
                false,
                Term::Rewrite {
                    left: Box::new(fresh_counter()),
                    right: Box::new(Term::apply(
                        "_+Int_",
                        vec![
                            fresh_counter(),
                            Term::Token {
                                token: count.to_string(),
                                sort: Sort::builtin(BuiltinSort::Int),
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
        && label.is(InternalLabel::WithConfig)
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
    let TermParts::Rewrite { left, right } = body.into_unannotated().into_parts() else {
        return Err("Malformed generated top-cell initializer rule".into());
    };
    let TermParts::Apply {
        label,
        mut arguments,
    } = right.into_unannotated().into_parts()
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
    cells.push(Term::apply(
        GeneratedCell::Counter.initializer(),
        Vec::new(),
    ));
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
        .is_some_and(|label| label.name == GeneratedCell::Top.label())
        && !items.iter().any(|item| {
            matches!(
                item,
                ProductionItem::NonTerminal { sort, .. }
                    if sort.name == BuiltinSort::GeneratedCounterCell.k_name()
            )
        })
    {
        let position = items.len().saturating_sub(1);
        items.insert(
            position,
            ProductionItem::NonTerminal {
                sort: Sort::builtin(BuiltinSort::GeneratedCounterCell),
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
    if label.name != GeneratedCell::Top.label() {
        return;
    }
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "ProductionItem is syntax; only the listed variants are special here"
    )]
    let positions = items
        .iter()
        .enumerate()
        .filter_map(|(index, item)| match item {
            ProductionItem::NonTerminal { sort, .. }
                if sort.name != BuiltinSort::GeneratedCounterCell.k_name() =>
            {
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
    attributes.set(AttributeKey::Format, json!(format));
}

/// The configuration `<generatedTop> <root/> <generatedCounter> N </generatedCounter>
/// </generatedTop>` around the module's root cell, with the counter cell only when `counter`
/// gives its initial value.
fn generated_top_configuration(
    definition: &ResolvedDefinition,
    module: crate::definition::ModuleId,
    productions: &ProductionCatalog<'_>,
    counter: Option<usize>,
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
            } if attributes.has(AttributeKey::Cell) => Some((label, attributes)),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
        })
        .ok_or_else(|| format!("No cell production found for root sort {root_sort}"))?;
    let cell_name = root
        .1
        .string(AttributeKey::CellName)
        .ok_or_else(|| format!("Root cell {} has no cellName attribute", root.0.name))?;
    let name = cell_name_token(GeneratedCell::Top.name());
    let root = Term::apply(
        InternalLabel::ExternalCell.as_str(),
        vec![cell_name_token(cell_name)],
    );
    let contents = match counter {
        Some(initial_fresh) => Term::apply(
            InternalLabel::Cells.as_str(),
            vec![root, counter_config_term(initial_fresh)],
        ),
        None => root,
    };
    Ok(configuration(Term::apply(
        InternalLabel::ConfigCell.as_str(),
        vec![
            name.clone(),
            Term::apply(
                InternalLabel::CellPropertyListTerminator.as_str(),
                Vec::new(),
            ),
            contents,
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
            } if attributes.has(AttributeKey::Cell) => Some(sort.clone()),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
        })
        .collect::<BTreeSet<_>>();
    let collections = productions
        .productions()
        .filter_map(|(_, production)| match production {
            Sentence::Production {
                sort, attributes, ..
            } if attributes.has(AttributeKey::CellCollection) => Some(sort.clone()),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
        })
        .collect::<BTreeSet<_>>();
    let subsorts = definition
        .subsorts(module)
        .map_err(|error| error.to_string())?;
    let mut children = BTreeSet::new();
    // Invariant: `children` holds every cell sort that is a direct child, as a cell nonterminal or as a cell directly below a cell-collection nonterminal, of a cell production of `productions` before this one; each iteration consumes one production.
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
        if !attributes.has(AttributeKey::Cell) || !cells.contains(sort) {
            continue;
        }
        // Invariant: `children` has gained the sort of every earlier nonterminal of `items` that is in `cells`, and each cell of `cells` directly below every earlier nonterminal in `collections`; each iteration consumes one item, and the collection case scans `cells`.
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
    let name = cell_name_token(GeneratedCell::Counter.name());
    Term::apply(
        InternalLabel::ConfigCell.as_str(),
        vec![
            name.clone(),
            Term::apply(
                InternalLabel::CellPropertyListTerminator.as_str(),
                Vec::new(),
            ),
            Term::Token {
                token: initial_fresh.to_string(),
                sort: Sort::builtin(BuiltinSort::Int),
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
        sort: Some(Sort::builtin(BuiltinSort::GeneratedCounterCell)),
    };
    [
        Sentence::Production {
            label: Some(Label::new("getGeneratedCounterCell")),
            parameters: Vec::new(),
            sort: Sort::builtin(BuiltinSort::GeneratedCounterCell),
            items: vec![
                ProductionItem::Terminal("getGeneratedCounterCell".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::builtin(BuiltinSort::GeneratedTopCell),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes: Attributes::from_pairs([(AttributeKey::Function, json!(""))]),
        },
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply(
                    "getGeneratedCounterCell",
                    vec![incomplete_cell(
                        GeneratedCell::Top.label(),
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
            Term::apply(
                if open_left {
                    InternalLabel::Dots
                } else {
                    InternalLabel::NoDots
                }
                .as_str(),
                Vec::new(),
            ),
            body,
            Term::apply(
                if open_right {
                    InternalLabel::Dots
                } else {
                    InternalLabel::NoDots
                }
                .as_str(),
                Vec::new(),
            ),
        ],
    )
}

fn fresh_counter() -> Term {
    Term::Variable {
        name: "#Fresh".into(),
        sort: Some(Sort::builtin(BuiltinSort::Int)),
    }
}

fn cell_name_token(name: &str) -> Term {
    Term::Token {
        token: name.into(),
        sort: Sort::frontend(FrontendSort::CellName),
    }
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}

fn rule_body(sentence: &Sentence) -> &Term {
    match sentence {
        Sentence::Rule { body, .. } => body,
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => unreachable!(),
    }
}

fn rewrite_left(term: &Term) -> Term {
    let metadata = term.metadata().cloned();
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
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
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    fn as_apply(&self) -> Option<(&Label, &[Term])> {
        match self.unannotated() {
            Term::Apply { label, arguments } => Some((label, arguments)),
            _ => None,
        }
    }
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
        input_addresses: Vec::new(),
    }
}

fn error_from(message: String) -> ResolveFreshConstantsError {
    ResolveFreshConstantsError {
        diagnostics: vec![plain_error(message)],
    }
}

/// The stage on the definition the pipeline gives it ([`crate::kompile::stage_harness`]).
#[cfg(test)]
mod stage_tests {
    use crate::kompile::CompileError;
    use crate::kompile::stage_harness::{labelled, render, rendered_changes, run_to_stage};

    /// `!X:S` denotes a value of `S` no earlier step has produced (K's user manual,
    /// `freshGenerator` attribute). The stage draws it from a counter cell the configuration
    /// gains for the purpose: the `n`-th fresh variable of a rule is the sort's generator
    /// applied to `counter + n`, and the rule advances the counter by the number of values it
    /// draws, so two variables of one step, and the values of two steps, never coincide.
    #[test]
    fn fresh_variables_are_distinct_counter_offsets_and_the_rule_advances_the_counter() {
        let run = run_to_stage(
            r#"
module INT
endmodule
module MAIN
  syntax K
  syntax Int ::= r"[0-9]+" [token]
  syntax Id ::= r"[a-z]+" [token]
              | freshId(Int) [function, freshGenerator, symbol(freshId)]
  syntax Exp ::= Int | Id | "go" [symbol(go)] | pair(Id, Id) [symbol(pair)]
  configuration <t> <k> go </k> <s> 0 </s> </t>
  rule <k> go => pair(!X:Id, !Y:Id) </k> [label(fresh)]
endmodule
"#,
            "resolve fresh constants",
        );
        assert_eq!(
            render(labelled(run.output(), "MAIN", "fresh")[0]),
            r#"rule #cells(`<k>`(#noDots(.KList),go(.KList)=>pair(freshId(`_+Int_`(#Fresh,#token("0","Int"))),freshId(`_+Int_`(#Fresh,#token("1","Int")))),#noDots(.KList)),`<generatedCounter>`(#noDots(.KList),#Fresh=>`_+Int_`(#Fresh,#token("2","Int")),#noDots(.KList))) requires #token("true","Bool") ensures #token("true","Bool")"#
        );
        // The counter cell starts at 0 and sits beside the user's top cell under a generated top.
        let (added, _) = rendered_changes(&run);
        for generated in [
            "syntax GeneratedCounterCell ::= <generatedCounter>(Int)",
            "syntax GeneratedTopCell ::= <generatedTop>(TCell, GeneratedCounterCell)",
            r#"rule initGeneratedCounterCell(.KList)=>`<generatedCounter>`(#noDots(.KList),#token("0","Int"),#noDots(.KList)) requires #token("true","Bool") ensures #token("true","Bool")"#,
            r#"rule initGeneratedTopCell(.KList)=>`<generatedTop>`(#noDots(.KList),#cells(initTCell(.KList),initGeneratedCounterCell(.KList)),#noDots(.KList)) requires #token("true","Bool") ensures #token("true","Bool")"#,
        ] {
            assert!(
                added.iter().any(|sentence| sentence == generated),
                "{generated}\n{added:#?}"
            );
        }
    }

    /// A local function's fresh closure variable reaches this stage as an argument of the
    /// lifted function's application in the enclosing rule (`resolve local functions`), so the
    /// rule that applies the function draws the value, once, at the call.
    #[test]
    fn a_fresh_argument_of_a_lifted_local_function_is_drawn_by_the_calling_rule() {
        let run = run_to_stage(
            r#"
module INT
endmodule
module MAIN
  syntax K
  syntax Int ::= r"[0-9]+" [token]
              | plus(Int, Int) [function, symbol(plus)]
              | freshInt(Int) [function, freshGenerator, symbol(freshInt)]
  syntax KItem ::= "go" [symbol(go)]
  configuration <k> go </k>
  rule <k> go => #fun(Y => plus(Y, !X:Int))(1) ...</k> [label(go)]
endmodule
"#,
            "resolve fresh constants",
        );
        assert_eq!(
            render(labelled(&run.input, "MAIN", "go")[0]),
            r#"rule `<k>`(#noDots(.KList),go(.KList)=>`#lambda__`(#token("1","Int"),!X),#dots(.KList)) requires #token("true","Bool") ensures #token("true","Bool")"#
        );
        assert_eq!(
            render(labelled(run.output(), "MAIN", "go")[0]),
            r#"rule #cells(`<k>`(#noDots(.KList),go(.KList)=>`#lambda__`(#token("1","Int"),freshInt(`_+Int_`(#Fresh,#token("0","Int")))),#dots(.KList)),`<generatedCounter>`(#noDots(.KList),#Fresh=>`_+Int_`(#Fresh,#token("1","Int")),#noDots(.KList))) requires #token("true","Bool") ensures #token("true","Bool")"#
        );
    }

    /// The counter cell holds an `Int`. When the main module sees no `Int`, nothing can draw
    /// from it (a generator takes an `Int`, the advance is `_+Int_`), and its declaration would
    /// name an undeclared sort: the generated top holds the user's top cell alone.
    #[test]
    fn without_int_the_generated_top_holds_no_counter_cell() {
        let run = run_to_stage(
            r#"
module MAIN
  syntax K
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)]
  configuration <t> <k> .K </k> <mem> a </mem> </t>
  rule <mem> a => b </mem> [label(step)]
endmodule
"#,
            "resolve fresh constants",
        );
        let (added, _) = rendered_changes(&run);
        assert!(
            added
                .iter()
                .any(|sentence| sentence == "syntax GeneratedTopCell ::= <generatedTop>(TCell)"),
            "{added:#?}"
        );
        assert!(
            added.iter().all(|sentence| !sentence.contains("Counter")),
            "{added:#?}"
        );
        assert_eq!(
            render(labelled(run.output(), "MAIN", "step")[0]),
            render(labelled(&run.input, "MAIN", "step")[0])
        );
    }

    /// The counter starts at the domain value `0` of `Int`. When the main module's `Int` has no
    /// domain values (only constructors), the configuration has no counter cell, and a fresh
    /// variable, which has nothing to draw from, is an error at its rule.
    #[test]
    fn a_fresh_variable_without_the_counter_cell_is_rejected_at_the_rule() {
        let run = run_to_stage(
            r#"
module INT
  syntax Int ::= "zero" [symbol(zero)]
               | Int "+Int" Int [function, symbol(_+Int_)]
endmodule
module MAIN
  imports INT
  syntax K
  syntax Id ::= r"[a-z]+" [token]
              | freshId(Int) [function, freshGenerator, symbol(freshId)]
  syntax KItem ::= "go" [symbol(go)]
  configuration <k> go </k>
  rule <k> go => !X:Id </k> [label(go)]
endmodule
"#,
            "resolve fresh constants",
        );
        let CompileError { diagnostics, .. } = run.error();
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("{diagnostics:#?}");
        };
        assert_eq!(
            diagnostic.message,
            "A fresh variable draws its value from the fresh counter cell, which holds an Int starting at the domain value 0, but the main module MAIN sees no sort Int with domain values, so the configuration has no counter cell."
        );
        assert_eq!(
            diagnostic
                .location
                .as_ref()
                .map(|location| location.start_line),
            Some(13)
        );
    }
}
