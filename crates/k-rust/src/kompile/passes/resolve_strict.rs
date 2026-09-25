//! ```toml algorithm
//! id = "kompile.strictness.resolve"
//! name = "lowering of strictness attributes"
//! sites = ["resolve_strict", "resolve_strict_pass", "resolve_production", "generate_contexts"]
//! variable = "L = local sentences; P = strict productions; k = strict positions per production; a = context aliases; C = generated evaluation contexts"
//! counters = []
//! no_counter = "strictness lowering has no dedicated counter"
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(L + P x k^2 x a + C^2)"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Generate evaluation contexts from `strict`, `seqstrict`, and `hybrid` productions.

use crate::provenance::extend_unique_sentences as extend_unique;
use std::{collections::BTreeMap, fmt, sync::Arc};

use serde_json::Value;

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, FlatImport, ProductionItem, ResolvedDefinition, Sentence,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{FrontendSort, Label, Sort, Term, WellKnownModule, parser::parse_sort},
    provenance::{GeneratingPass, seed_generated_sentence_origin, sentence_origin_links},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveStrictError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveStrictError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "strictness resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveStrictError {}

#[derive(Clone)]
struct Alias {
    body: Term,
    requires: Term,
    attributes: Attributes,
}

/// Apply Java's `ResolveStrict` definition transformation.
pub fn resolve_strict(definition: &Definition) -> Result<Definition, ResolveStrictError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_strict_pass,
        Some(GeneratingPass::ResolveStrict),
    )
}

pub(crate) fn resolve_strict_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveStrictError> {
    let resolved = input.resolved_raw().map_err(|error| ResolveStrictError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let main = resolved.main_module_id();
    let aliases = labeled_sentences(resolved, main);
    let bool_module = resolved.module_id(WellKnownModule::Bool.as_str());
    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();

    // Invariant: every module of `output.modules` before `module` has lost its context aliases and gained its generated strictness contexts, and `diagnostics` holds their errors; each iteration consumes one module.
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let mut generated = Vec::new();
        // Invariant: `generated` holds, without duplicates, the contexts resolved from every `strict` or `seqstrict` production of `module.local_sentences` before `sentence`, and `diagnostics` their errors; each iteration consumes one sentence.
        for sentence in &module.local_sentences {
            let Sentence::Production { attributes, .. } = &**sentence else {
                continue;
            };
            for (key, sequential) in [
                (AttributeKey::Strict, false),
                (AttributeKey::Seqstrict, true),
            ] {
                if !attributes.has(key) {
                    continue;
                }
                match resolve_production(sentence, key, sequential, &module.name, &aliases) {
                    Ok(sentences) => extend_unique(&mut generated, sentences),
                    Err(mut errors) => diagnostics.append(&mut errors),
                }
            }
        }

        module
            .local_sentences
            .retain(|sentence| !matches!(&**sentence, Sentence::ContextAlias { .. }));
        if !generated.is_empty() {
            let imports_bool = bool_module.is_some_and(|bool_module| {
                resolved
                    .transitive_imports(module_id)
                    .contains(&bool_module)
                    || module_id == bool_module
            });
            if !imports_bool {
                if bool_module.is_some() {
                    module.imports.insert(
                        0,
                        FlatImport {
                            name: WellKnownModule::Bool.as_str().into(),
                            public: false,
                        },
                    );
                } else {
                    diagnostics.push(error_at(
                        format!(
                            "Strictness-generated contexts require the missing module {}.",
                            WellKnownModule::Bool.as_str()
                        ),
                        &module.attributes,
                    ));
                }
            }
            module
                .local_sentences
                .extend(generated.into_iter().map(Arc::new));
        }
    }

    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(ResolveStrictError { diagnostics })
    }
}

fn resolve_production(
    production: &Sentence,
    key: AttributeKey,
    sequential: bool,
    module_name: &str,
    labeled: &BTreeMap<String, Vec<&Sentence>>,
) -> Result<Vec<Sentence>, Vec<Diagnostic>> {
    let Sentence::Production {
        label,
        items,
        attributes,
        ..
    } = production
    else {
        unreachable!()
    };
    let Some(label) = label else {
        return Err(vec![error_at(
            "Only productions with a KLabel can be strict.",
            attributes,
        )]);
    };
    let nonterminals = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let arity = nonterminals.len();
    let attribute = attribute_text(attributes, key).unwrap_or_default();
    let mut all_positions = Vec::new();
    let mut generated = Vec::new();

    if attribute.is_empty() {
        let positions = (1..=arity).collect::<Vec<_>>();
        let aliases = vec![default_alias(attributes)];
        generate_contexts(
            &mut generated,
            sequential,
            &positions,
            &all_positions,
            &aliases,
            label,
            &nonterminals,
            attributes,
            module_name,
        )?;
        all_positions.extend(positions);
    } else {
        let components = java_split(&attribute, ';');
        if components.len() == 1 {
            let component = components[0].trim();
            let (positions, aliases) = if component
                .chars()
                .next()
                .is_some_and(|character| character.is_ascii_digit())
            {
                (
                    parse_positions(component, arity, attributes)?,
                    vec![default_alias(attributes)],
                )
            } else {
                (
                    (1..=arity).collect(),
                    resolve_aliases(component, production, labeled)?,
                )
            };
            generate_contexts(
                &mut generated,
                sequential,
                &positions,
                &all_positions,
                &aliases,
                label,
                &nonterminals,
                attributes,
                module_name,
            )?;
            all_positions.extend(positions);
        } else if components.len().is_multiple_of(2) {
            for pair in components.as_chunks::<2>().0 {
                let aliases = resolve_aliases(pair[0].trim(), production, labeled)?;
                let positions = parse_positions(pair[1].trim(), arity, attributes)?;
                generate_contexts(
                    &mut generated,
                    sequential,
                    &positions,
                    &all_positions,
                    &aliases,
                    label,
                    &nonterminals,
                    attributes,
                    module_name,
                )?;
                all_positions.extend(positions);
            }
        } else {
            return Err(vec![error_at(
                "Invalid strict attribute containing multiple semicolons.",
                attributes,
            )]);
        }
    }

    if attributes.has(AttributeKey::Hybrid) {
        let hybrid = attribute_text(attributes, AttributeKey::Hybrid).unwrap_or_default();
        let predicates = if hybrid.is_empty() {
            vec!["isKResult".to_owned()]
        } else {
            java_split(&hybrid, ',')
                .into_iter()
                .map(|sort| Label::sort_predicate(&Sort::new(sort.trim())).name)
                .collect()
        };
        for predicate in predicates {
            let arguments = nonterminals
                .iter()
                .enumerate()
                .map(|(index, sort)| semantic_cast(sort, Term::variable(format!("K{index}"))))
                .collect();
            let term = Term::Apply {
                label: label.clone(),
                arguments,
            };
            let side_conditions = all_positions.iter().map(|position| {
                Term::apply(
                    &predicate,
                    vec![Term::variable(format!("K{}", position - 1))],
                )
            });
            generated.push(Sentence::Rule {
                body: Term::Rewrite {
                    left: Box::new(Term::apply(&predicate, vec![term])),
                    right: Box::new(bool_token(true)),
                },
                requires: reduce_and(side_conditions).unwrap_or_else(|| bool_token(true)),
                ensures: bool_token(true),
                attributes: Attributes::default(),
            });
        }
    }

    let origins = sentence_origin_links(production);
    // Every generated sentence derives from the production; a context also derives from the
    // context alias it instantiates, whose addresses `merge_attributes` already added after the
    // production's.
    for sentence in &mut generated {
        sentence
            .attributes_mut()
            .union_input_addresses(production.attributes());
        seed_generated_sentence_origin(sentence, GeneratingPass::ResolveStrict, origins.clone());
    }
    Ok(generated)
}

#[allow(clippy::too_many_arguments)]
fn generate_contexts(
    generated: &mut Vec<Sentence>,
    sequential: bool,
    positions: &[usize],
    all_positions: &[usize],
    aliases: &[Alias],
    production_label: &Label,
    nonterminals: &[Sort],
    production_attributes: &Attributes,
    module_name: &str,
) -> Result<(), Vec<Diagnostic>> {
    // Invariant: `generated` holds, for every position of `positions` before `position_index`, one context per alias of `aliases`; each iteration consumes one position, and the inner loop over `aliases` makes the work O(`positions` * `aliases`).
    for (position_index, position) in positions.iter().copied().enumerate() {
        let strict_index = position - 1;
        let base_arguments = nonterminals
            .iter()
            .enumerate()
            .map(|(index, sort)| semantic_cast(sort, Term::variable(format!("K{index}"))))
            .collect::<Vec<_>>();
        let hole = semantic_cast(&nonterminals[strict_index], Term::variable("HOLE"));

        // Invariant: `generated` has gained one context at the strict position `position` for each alias of `aliases` before `alias`; each iteration consumes one alias.
        for alias in aliases {
            let mut arguments = base_arguments.clone();
            let mut this_hole = hole.clone();
            if let Some(context_label) = attribute_text(&alias.attributes, AttributeKey::Context) {
                this_hole = Term::Rewrite {
                    left: Box::new(hole.clone()),
                    right: Box::new(Term::apply(&context_label, vec![hole.clone()])),
                };
            }
            arguments[strict_index] = this_hole;
            let replacement = Term::Apply {
                label: production_label.clone(),
                arguments,
            };
            let body = replace_here(alias.body.clone(), &replacement);
            let result_text = attribute_text(&alias.attributes, AttributeKey::Result)
                .unwrap_or_else(|| FrontendSort::KResult.as_str().into());
            let result = parse_sort(&result_text).map_err(|error| {
                vec![error_at(
                    format!("Invalid result sort {result_text:?} in context alias: {error}"),
                    &alias.attributes,
                )]
            })?;
            let prior_positions = all_positions
                .iter()
                .chain(positions[..position_index].iter())
                .copied();
            let side_condition = reduce_and(prior_positions.map(|prior| Term::Apply {
                label: Label::sort_predicate(&result),
                arguments: vec![Term::variable(format!("K{}", prior - 1))],
            }));
            let requires = if sequential {
                side_condition.unwrap_or_else(|| bool_token(true))
            } else {
                bool_token(true)
            };
            let requires = Term::apply("_andBool_", vec![requires, alias.requires.clone()]);
            let mut attributes = merge_attributes(production_attributes, &alias.attributes);
            let source_label = attribute_text(production_attributes, AttributeKey::Klabel)
                .unwrap_or_else(|| production_label.name.clone());
            let compact_label = source_label
                .chars()
                .filter(|character| *character != '`' && !character.is_whitespace())
                .collect::<String>();
            attributes.set(
                AttributeKey::Label,
                Value::String(format!("{module_name}.{compact_label}{position}")),
            );
            generated.push(Sentence::Context {
                body,
                requires,
                attributes,
            });
        }
    }
    Ok(())
}

fn parse_positions(
    text: &str,
    arity: usize,
    attributes: &Attributes,
) -> Result<Vec<usize>, Vec<Diagnostic>> {
    let raw = java_split(text, ',');
    let mut positions = Vec::new();
    for part in &raw {
        let position = part.trim().parse::<usize>().ok();
        let Some(position) = position.filter(|position| (1..=arity).contains(position)) else {
            let message = if arity == 0 {
                "Cannot put a strict attribute on a production with no nonterminals".into()
            } else {
                format!(
                    "Expecting a number between 1 and {arity}, but found {} as a strict position in [{}]",
                    part.trim(),
                    raw.join(", ")
                )
            };
            return Err(vec![error_at(message, attributes)]);
        };
        positions.push(position);
    }
    Ok(positions)
}

fn resolve_aliases(
    text: &str,
    production: &Sentence,
    labeled: &BTreeMap<String, Vec<&Sentence>>,
) -> Result<Vec<Alias>, Vec<Diagnostic>> {
    let mut aliases = Vec::<Alias>::new();
    // Invariant: `aliases` holds, without duplicates and in order, the context aliases named by every label of `text` before `raw_label`; each iteration consumes one comma-separated label, and the inner loop over its `sentences` checks each alias against `aliases`, quadratic in the number of aliases.
    for raw_label in java_split(text, ',') {
        let label = raw_label.trim();
        let Some(sentences) = labeled.get(label) else {
            return Err(vec![error_at(
                format!(
                    "Found rule label \"{label}\" in strictness attribute which did not refer to any sentence."
                ),
                production.attributes(),
            )]);
        };
        for sentence in sentences {
            let Sentence::ContextAlias {
                body,
                requires,
                attributes,
            } = sentence
            else {
                return Err(vec![error_at(
                    format!(
                        "Found rule label \"{label}\" in strictness attribute of production which does not refer to a context alias."
                    ),
                    sentence.attributes(),
                )]);
            };
            let alias = Alias {
                body: body.clone(),
                requires: requires.clone(),
                attributes: attributes.clone(),
            };
            match aliases.iter_mut().find(|existing| {
                existing.body == alias.body
                    && existing.requires == alias.requires
                    && existing.attributes == alias.attributes
            }) {
                // Equal aliases instantiate to one context, which derives from both.
                Some(existing) => existing.attributes.union_input_addresses(&alias.attributes),
                None => aliases.push(alias),
            }
        }
    }
    Ok(aliases)
}

fn labeled_sentences(
    definition: &ResolvedDefinition,
    module: crate::definition::ModuleId,
) -> BTreeMap<String, Vec<&Sentence>> {
    let mut labeled = BTreeMap::<String, Vec<&Sentence>>::new();
    for sentence in definition.sentences(module) {
        if let Some(label) = attribute_text(sentence.attributes(), AttributeKey::Label) {
            labeled.entry(label).or_default().push(sentence);
        }
    }
    labeled
}

fn default_alias(production_attributes: &Attributes) -> Alias {
    let mut attributes = Attributes::default();
    if let Some(result) = production_attributes.value(AttributeKey::Result) {
        attributes.set(AttributeKey::Result, result.clone());
    }
    Alias {
        body: Term::variable("HERE"),
        requires: bool_token(true),
        attributes,
    }
}

fn replace_here(term: Term, replacement: &Term) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            replace_here(*term, replacement).with_metadata(metadata)
        }
        Term::Variable { name, .. } if name == "HERE" => replacement.clone(),
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(replace_here(*left, replacement)),
            right: Box::new(replace_here(*right, replacement)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(replace_here(*pattern, replacement)),
            alias: Box::new(replace_here(*alias, replacement)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| replace_here(item, replacement))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| replace_here(argument, replacement))
                .collect(),
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
    }
}

fn semantic_cast(sort: &Sort, term: Term) -> Term {
    Term::Apply {
        label: Label::semantic_cast(sort),
        arguments: vec![term],
    }
}

fn reduce_and(terms: impl IntoIterator<Item = Term>) -> Option<Term> {
    terms
        .into_iter()
        .reduce(|left, right| Term::apply("_andBool_", vec![left, right]))
}

fn merge_attributes(left: &Attributes, right: &Attributes) -> Attributes {
    let mut result = left.clone();
    for (key, value) in right.semantic_entries() {
        result.insert(key, value.clone());
    }
    result.inherit_origin(right);
    result.union_input_addresses(right);
    result
}

fn attribute_text(attributes: &Attributes, key: AttributeKey) -> Option<String> {
    attributes.value(key).map(|value| match value {
        Value::String(value) => value.clone(),
        Value::Null => String::new(),
        value => value.to_string(),
    })
}

fn java_split(text: &str, delimiter: char) -> Vec<&str> {
    let mut values = text.split(delimiter).collect::<Vec<_>>();
    // Invariant: `values` is `text` split at `delimiter` with some trailing empty strings removed, and keeps at least one element; each iteration pops one element.
    while values.len() > 1 && values.last() == Some(&"") {
        values.pop();
    }
    values
}

fn bool_token(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}

fn error_at(message: impl Into<String>, attributes: &Attributes) -> Diagnostic {
    Diagnostic::error_at(DiagnosticCode::InvalidStrictness, message, attributes)
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidStrictness,
        message: message.into(),
        source: None,
        location: None,
    }
}
