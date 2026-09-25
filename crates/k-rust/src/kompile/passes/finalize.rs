//! ```toml algorithm-site
//! id = "kompile.sort_helpers.generate"
//! role = "part"
//! sites = ["generate_sort_predicate_rules", "generate_sort_predicate_rules_pass"]
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Final definition-wide transformations before KORE emission.

use std::{collections::BTreeSet, convert::Infallible};

use serde_json::Value;

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, FlatImport, FlatModule, LabelHead, Sentence,
        extend_with_new_sentences,
    },
    kast::{Sort, Term, WellKnownModule},
    provenance::GeneratingPass,
};

/// Add Java's synthetic `LANGUAGE-PARSING` module.
///
/// Full installations provide all four imports. Standalone `--no-prelude` definitions retain the
/// same module boundary while importing only modules that actually exist.
pub fn add_semantics_module(definition: &Definition) -> Result<Definition, Infallible> {
    super::super::pipeline::run_standalone(definition, add_semantics_module_pass, None)
}

pub(crate) fn add_semantics_module_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, Infallible> {
    let definition = input.definition;
    if definition
        .modules
        .iter()
        .any(|module| module.name == WellKnownModule::LanguageParsing.as_str())
    {
        return Ok(definition.clone());
    }
    let available = definition
        .modules
        .iter()
        .map(|module| module.name.as_str())
        .collect::<BTreeSet<_>>();
    let syntax_module = definition.attributes.string(AttributeKey::SyntaxModule);
    let imports = [
        Some(definition.main_module.as_str()),
        syntax_module,
        Some("K-TERM"),
        Some("ID-SYNTAX-PROGRAM-PARSING"),
    ]
    .into_iter()
    .flatten()
    .filter(|name| available.contains(name))
    // Invariant: `imports` lists, once each and in candidate order, every available module name folded so far; each step consumes one name of the four-element candidate list.
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
        name: WellKnownModule::LanguageParsing.as_str().into(),
        imports,
        local_sentences: Vec::new(),
        attributes: Attributes::default(),
    });
    Ok(output)
}

/// Mark rules and contexts whose left side begins with a variable in a main-cell K sequence.
///
/// `KoreBackend` applies `new AddCoolLikeAtt(d.mainModule())` to every module's sentences, so the
/// `maincell` attribute is looked up in the main module's productions for every rule, including
/// the rules of an imported module that does not see the generated configuration itself.
pub fn add_cool_like_attributes(definition: &Definition) -> Definition {
    super::super::pipeline::run_standalone(definition, add_cool_like_attributes_pass, None)
        .unwrap_or_else(|error| match error {})
}

pub(crate) fn add_cool_like_attributes_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, Infallible> {
    let Ok(resolved) = input.resolved_raw() else {
        return Ok(input.definition.clone());
    };
    let productions = resolved.production_catalog(resolved.main_module_id());
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            let sentence = crate::definition::sentence_mut(sentence);
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
                        attributes.mark(AttributeKey::CoolLike);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
    Ok(output)
}

/// Generate Java's final positive and `owise` negative sort-predicate rules.
pub fn generate_sort_predicate_rules(definition: &Definition) -> Definition {
    super::super::pipeline::run_standalone(
        definition,
        generate_sort_predicate_rules_pass,
        Some(GeneratingPass::GenerateSortPredicateRules),
    )
    .unwrap_or_else(|error| match error {})
}

pub(crate) fn generate_sort_predicate_rules_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, Infallible> {
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let predicates = module
            .local_sentences
            .iter()
            .filter_map(|sentence| match &**sentence {
                Sentence::Production {
                    label: Some(label),
                    attributes,
                    ..
                } => attributes
                    .value(AttributeKey::Predicate)
                    .and_then(sort_from_json)
                    .map(|sort| (label.name.clone(), sort)),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut generated = Vec::new();
        // Invariant: `generated` holds the predicate rules of every `(predicate, sort)` pair of `predicates` before this one, one rule for the `K` sort and two otherwise; each iteration consumes one pair of the finite set `predicates`.
        for (predicate, sort) in predicates {
            if sort.is_builtin(BuiltinSort::K) {
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
        extend_with_new_sentences(&mut module.local_sentences, generated);
    }
    Ok(output)
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

// Invariant: the result is true when `term` or a subterm is a `Maincell` application whose first argument is a sequence of at least two items starting with a variable; each call recurses into the immediate subterms of `term` and stops at the first match.
fn contains_cool_like(term: &Term, productions: &crate::definition::ProductionCatalog<'_>) -> bool {
    match term.unannotated() {
        Term::Apply { label, arguments } => {
            let main_cell = productions
                .attributes_for(&LabelHead::from(label))
                .is_some_and(|attributes| attributes.has(AttributeKey::Maincell));
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
        attributes.mark(AttributeKey::Owise);
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
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}
