//! Final definition-wide transformations before KORE emission.

use std::collections::BTreeSet;

use serde_json::{Value, json};

use crate::{
    definition::{
        Attributes, Definition, FlatImport, FlatModule, LabelHead, ResolvedDefinition, Sentence,
    },
    kast::{Sort, Term},
    provenance::{GeneratingPass, record_generated_origins},
};

const LANGUAGE_PARSING: &str = "LANGUAGE-PARSING";

/// Add Java's synthetic `LANGUAGE-PARSING` module.
///
/// Full installations provide all four imports. Standalone `--no-prelude` definitions retain the
/// same module boundary while importing only modules that actually exist.
pub fn add_semantics_module(definition: &Definition) -> Definition {
    if definition
        .modules
        .iter()
        .any(|module| module.name == LANGUAGE_PARSING)
    {
        return definition.clone();
    }
    let available = definition
        .modules
        .iter()
        .map(|module| module.name.as_str())
        .collect::<BTreeSet<_>>();
    let syntax_module = definition.attributes.get_str("syntaxModule");
    let imports = [
        Some(definition.main_module.as_str()),
        syntax_module,
        Some("K-TERM"),
        Some("ID-SYNTAX-PROGRAM-PARSING"),
    ]
    .into_iter()
    .flatten()
    .filter(|name| available.contains(name))
    .fold(Vec::<FlatImport>::new(), |mut imports, name| {
        if !imports.iter().any(|import| import.name == name) {
            imports.push(FlatImport {
                name: name.to_owned(),
                public: true,
            });
        }
        imports
    });
    let mut output = definition.clone();
    output.modules.push(FlatModule {
        name: LANGUAGE_PARSING.into(),
        imports,
        local_sentences: Vec::new(),
        attributes: Attributes::default(),
    });
    output
}

/// Mark rules and contexts whose left side begins with a variable in a main-cell K sequence.
pub fn add_cool_like_attributes(definition: &Definition) -> Definition {
    let Ok(resolved) = ResolvedDefinition::resolve(definition) else {
        return definition.clone();
    };
    let mut output = definition.clone();
    for module in &mut output.modules {
        let Some(module_id) = resolved.module_id(&module.name) else {
            continue;
        };
        let productions = resolved.production_catalog(module_id);
        for sentence in &mut module.local_sentences {
            let body = match sentence {
                Sentence::Rule { body, .. }
                | Sentence::Context { body, .. }
                | Sentence::ContextAlias { body, .. } => body,
                _ => continue,
            };
            if contains_cool_like(project_left(body), &productions) {
                match sentence {
                    Sentence::Rule { attributes, .. }
                    | Sentence::Context { attributes, .. }
                    | Sentence::ContextAlias { attributes, .. } => {
                        attributes.insert("cool-like", json!(""));
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
    output
}

/// Generate Java's final positive and `owise` negative sort-predicate rules.
pub fn generate_sort_predicate_rules(definition: &Definition) -> Definition {
    let mut output = definition.clone();
    for module in &mut output.modules {
        let predicates = module
            .local_sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::Production {
                    label: Some(label),
                    attributes,
                    ..
                } => attributes
                    .get("predicate")
                    .and_then(sort_from_json)
                    .map(|sort| (label.name.clone(), sort)),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut generated = Vec::new();
        for (predicate, sort) in predicates {
            if sort.name == "K" && sort.parameters.is_empty() {
                generated.push(predicate_rule(
                    &predicate,
                    Term::Variable {
                        name: "K".into(),
                        sort: None,
                    },
                    true,
                    false,
                ));
            } else {
                generated.push(predicate_rule(
                    &predicate,
                    Term::Variable {
                        name: sort.name.clone(),
                        sort: Some(sort),
                    },
                    true,
                    false,
                ));
                generated.push(predicate_rule(
                    &predicate,
                    Term::Variable {
                        name: "K".into(),
                        sort: None,
                    },
                    false,
                    true,
                ));
            }
        }
        for sentence in generated {
            if !module.local_sentences.contains(&sentence) {
                module.local_sentences.push(sentence);
            }
        }
    }
    record_generated_origins(
        definition,
        output,
        GeneratingPass::GenerateSortPredicateRules,
    )
}

fn sort_from_json(value: &Value) -> Option<Sort> {
    let object = value.as_object()?;
    if object.get("node")?.as_str()? != "KSort" {
        return None;
    }
    Some(Sort::with_parameters(
        object.get("name")?.as_str()?,
        object
            .get("params")?
            .as_array()?
            .iter()
            .map(sort_from_json)
            .collect::<Option<Vec<_>>>()?,
    ))
}

fn contains_cool_like(term: &Term, productions: &crate::definition::ProductionCatalog<'_>) -> bool {
    match term.unannotated() {
        Term::Apply { label, arguments } => {
            let main_cell = productions
                .attributes_for(&LabelHead::from(label))
                .is_some_and(|attributes| attributes.get("maincell").is_some());
            let starts_with_variable = arguments.first().is_some_and(|argument| {
                matches!(argument.unannotated(), Term::Sequence(items)
                    if items.len() > 1
                        && starts_with_variable(project_left(&items[0])))
            });
            (main_cell && starts_with_variable)
                || arguments
                    .iter()
                    .any(|argument| contains_cool_like(argument, productions))
        }
        Term::Rewrite { left, right } => {
            contains_cool_like(left, productions) || contains_cool_like(right, productions)
        }
        Term::As { pattern, alias } => {
            contains_cool_like(pattern, productions) || contains_cool_like(alias, productions)
        }
        Term::Sequence(items) => items
            .iter()
            .any(|item| contains_cool_like(item, productions)),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => false,
        Term::Annotated { .. } => unreachable!(),
    }
}

fn starts_with_variable(term: &Term) -> bool {
    match project_left(term).unannotated() {
        Term::Variable { .. } => true,
        Term::Sequence(items) => items.first().is_some_and(starts_with_variable),
        _ => false,
    }
}

fn project_left(term: &Term) -> &Term {
    match term.unannotated() {
        Term::Rewrite { left, .. } => project_left(left),
        _ => term,
    }
}

fn predicate_rule(predicate: &str, argument: Term, result: bool, owise: bool) -> Sentence {
    let mut attributes = Attributes::default();
    if owise {
        attributes.insert("owise", json!(""));
    }
    Sentence::Rule {
        body: Term::Rewrite {
            left: Box::new(Term::apply(predicate, vec![argument])),
            right: Box::new(bool_token(result)),
        },
        requires: bool_token(true),
        ensures: bool_token(true),
        attributes,
    }
}

fn bool_token(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Bool"),
    }
}
