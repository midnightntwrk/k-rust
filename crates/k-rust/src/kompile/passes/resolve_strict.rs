//! Generate evaluation contexts from `strict`, `seqstrict`, and `hybrid` productions.

use std::{collections::BTreeMap, fmt};

use serde_json::Value;

use crate::{
    definition::{
        Attributes, Definition, FlatImport, ProductionItem, ResolvedDefinition, Sentence,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term, parser::parse_sort},
    provenance::{
        GeneratingPass, record_generated_origins, seed_generated_sentence_origin,
        sentence_origin_links,
    },
};

const BOOL_MODULE: &str = "BOOL";

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
    resolve_strict_inner(definition)
        .map(|output| record_generated_origins(definition, output, GeneratingPass::ResolveStrict))
}

fn resolve_strict_inner(definition: &Definition) -> Result<Definition, ResolveStrictError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| ResolveStrictError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let main = resolved.main_module_id();
    let aliases = labeled_sentences(&resolved, main);
    let bool_module = resolved.module_id(BOOL_MODULE);
    let mut output = definition.clone();
    let mut diagnostics = Vec::new();

    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let mut generated = Vec::new();
        for sentence in &module.local_sentences {
            let Sentence::Production { attributes, .. } = sentence else {
                continue;
            };
            for (key, sequential) in [("strict", false), ("seqstrict", true)] {
                if attributes.get(key).is_none() {
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
            .retain(|sentence| !matches!(sentence, Sentence::ContextAlias { .. }));
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
                            name: BOOL_MODULE.into(),
                            public: false,
                        },
                    );
                } else {
                    diagnostics.push(error_at(
                        format!(
                            "Strictness-generated contexts require the missing module {BOOL_MODULE}."
                        ),
                        &module.attributes,
                    ));
                }
            }
            extend_unique(&mut module.local_sentences, generated);
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
    key: &str,
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
        } else if components.len() % 2 == 0 {
            for pair in components.chunks_exact(2) {
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

    if attributes.get("hybrid").is_some() {
        let hybrid = attribute_text(attributes, "hybrid").unwrap_or_default();
        let predicates = if hybrid.is_empty() {
            vec!["isKResult".to_owned()]
        } else {
            java_split(&hybrid, ',')
                .into_iter()
                .map(|sort| format!("is{}", sort.trim()))
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
    for sentence in &mut generated {
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
    for (position_index, position) in positions.iter().copied().enumerate() {
        let strict_index = position - 1;
        let base_arguments = nonterminals
            .iter()
            .enumerate()
            .map(|(index, sort)| semantic_cast(sort, Term::variable(format!("K{index}"))))
            .collect::<Vec<_>>();
        let hole = semantic_cast(&nonterminals[strict_index], Term::variable("HOLE"));

        for alias in aliases {
            let mut arguments = base_arguments.clone();
            let mut this_hole = hole.clone();
            if let Some(context_label) = attribute_text(&alias.attributes, "context") {
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
            let result_text =
                attribute_text(&alias.attributes, "result").unwrap_or_else(|| "KResult".into());
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
            let side_condition = reduce_and(prior_positions.map(|prior| {
                Term::apply(
                    format!("is{result}"),
                    vec![Term::variable(format!("K{}", prior - 1))],
                )
            }));
            let requires = if sequential {
                side_condition.unwrap_or_else(|| bool_token(true))
            } else {
                bool_token(true)
            };
            let requires = Term::apply("_andBool_", vec![requires, alias.requires.clone()]);
            let mut attributes = merge_attributes(production_attributes, &alias.attributes);
            let source_label = attribute_text(production_attributes, "klabel")
                .unwrap_or_else(|| production_label.name.clone());
            let compact_label = source_label
                .chars()
                .filter(|character| *character != '`' && !character.is_whitespace())
                .collect::<String>();
            attributes.insert(
                "label",
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
    let mut aliases = Vec::new();
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
            if !aliases.iter().any(|existing: &Alias| {
                existing.body == alias.body
                    && existing.requires == alias.requires
                    && existing.attributes == alias.attributes
            }) {
                aliases.push(alias);
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
        if let Some(label) = attribute_text(sentence.attributes(), "label") {
            labeled.entry(label).or_default().push(sentence);
        }
    }
    labeled
}

fn default_alias(production_attributes: &Attributes) -> Alias {
    let mut attributes = Attributes::default();
    if let Some(result) = production_attributes.get("result") {
        attributes.insert("result", result.clone());
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
    Term::apply(format!("#SemanticCastTo{sort}"), vec![term])
}

fn reduce_and(terms: impl IntoIterator<Item = Term>) -> Option<Term> {
    terms
        .into_iter()
        .reduce(|left, right| Term::apply("_andBool_", vec![left, right]))
}

fn merge_attributes(left: &Attributes, right: &Attributes) -> Attributes {
    let mut result = left.clone();
    for (key, value) in right.entries() {
        result.insert(key, value.clone());
    }
    result
}

fn attribute_text(attributes: &Attributes, key: &str) -> Option<String> {
    attributes.get(key).map(|value| match value {
        Value::String(value) => value.clone(),
        Value::Null => String::new(),
        value => value.to_string(),
    })
}

fn java_split(text: &str, delimiter: char) -> Vec<&str> {
    let mut values = text.split(delimiter).collect::<Vec<_>>();
    while values.len() > 1 && values.last() == Some(&"") {
        values.pop();
    }
    values
}

fn bool_token(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Bool"),
    }
}

fn extend_unique(target: &mut Vec<Sentence>, additions: impl IntoIterator<Item = Sentence>) {
    for sentence in additions {
        if !target.contains(&sentence) {
            target.push(sentence);
        }
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
