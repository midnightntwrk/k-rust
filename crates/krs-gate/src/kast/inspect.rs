//! Data-driven validation and inspection of losslessly read KAST.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::definition::{Attributes, Definition, Sentence};
use k_rust::kast::{Label, Sort, Term};
use sha2::{Digest, Sha256};

use super::reader::{self, DefinitionDocument, Document};
use serde::Deserialize;
use serde_json::{Value, json};

#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct TermValidationPolicy {
    #[serde(default)]
    pub labels: BTreeSet<String>,
    #[serde(default)]
    pub label_prefixes: Vec<String>,
    #[serde(default)]
    pub label_contains: Vec<String>,
    #[serde(default)]
    pub parameterized_sorts: bool,
    #[serde(default)]
    pub variables: bool,
}

pub(crate) fn validate_sort(sort: &Sort, policy: &TermValidationPolicy) -> Result<(), String> {
    if !policy.parameterized_sorts && !sort.parameters.is_empty() {
        return Err(format!("unsupported parameterized sort {:?}", sort.name));
    }
    for parameter in &sort.parameters {
        validate_sort(parameter, policy)?;
    }
    Ok(())
}

pub(crate) fn validate_label(label: &Label, policy: &TermValidationPolicy) -> Result<(), String> {
    if !policy.parameterized_sorts && !label.parameters.is_empty() {
        return Err(format!("unsupported parameterized label {:?}", label.name));
    }
    for parameter in &label.parameters {
        validate_sort(parameter, policy)?;
    }
    if policy.labels.contains(&label.name)
        || policy
            .label_prefixes
            .iter()
            .any(|prefix| label.name.starts_with(prefix))
        || policy
            .label_contains
            .iter()
            .any(|fragment| label.name.contains(fragment))
    {
        Ok(())
    } else {
        Err(format!("unrecognized project KLabel {:?}", label.name))
    }
}

pub(crate) fn validate_term(term: &Term, policy: &TermValidationPolicy) -> Result<(), String> {
    match term.unannotated() {
        Term::Apply { label, arguments } => {
            validate_label(label, policy)?;
            for argument in arguments {
                validate_term(argument, policy)?;
            }
        }
        Term::Token { sort, .. } => validate_sort(sort, policy)?,
        Term::Sequence(items) => {
            for item in items {
                validate_term(item, policy)?;
            }
        }
        Term::Variable {
            sort: Some(sort), ..
        } if policy.variables => validate_sort(sort, policy)?,
        _ => return Err(format!("unsupported KAST term {term:?}")),
    }
    Ok(())
}

pub(crate) fn abstract_term(
    term: &Term,
    names: &BTreeMap<String, String>,
) -> Result<Value, String> {
    match term.unannotated() {
        Term::Token { token, sort } => Ok(json!([sort.name, token])),
        Term::Apply { label, arguments } => {
            let name = names
                .get(&label.name)
                .ok_or_else(|| format!("unknown authored-tree label {:?}", label.name))?;
            let mut result = vec![json!(name)];
            for argument in arguments {
                result.push(abstract_term(argument, names)?);
            }
            Ok(Value::Array(result))
        }
        _ => Err(format!("unexpected authored-tree node {term:?}")),
    }
}

fn application(term: &Term) -> Result<(&str, &[Term]), String> {
    match term.unannotated() {
        Term::Apply { label, arguments } => Ok((&label.name, arguments)),
        _ => Err(format!("expected application, got {term:?}")),
    }
}

pub(crate) fn parse_map(term: &Term) -> Result<BTreeMap<String, String>, String> {
    let (label, arguments) = application(term)?;
    match label {
        ".Map" => Ok(BTreeMap::new()),
        "_Map_" => {
            let mut merged = BTreeMap::new();
            for child in arguments {
                for (key, value) in parse_map(child)? {
                    if merged.insert(key.clone(), value).is_some() {
                        return Err(format!("duplicate concrete map key {key:?}"));
                    }
                }
            }
            Ok(merged)
        }
        "_|->_" => {
            let [key, value] = arguments else {
                return Err("environment map entry requires two arguments".into());
            };
            let Term::Token { token: key, sort } = key.unannotated() else {
                return Err("non-Id environment key".into());
            };
            if sort.name != "Id" {
                return Err("non-Id environment key".into());
            }
            let Term::Token { token: value, sort } = value.unannotated() else {
                return Err("non-Value environment value".into());
            };
            if !matches!(sort.name.as_str(), "Int" | "Bool") {
                return Err("non-Value environment value".into());
            }
            Ok(BTreeMap::from([(key.clone(), value.clone())]))
        }
        _ => Err(format!("unsupported concrete Map label {label:?}")),
    }
}

pub(crate) fn final_environment(term: &Term) -> Result<BTreeMap<String, String>, String> {
    let (label, children) = application(term)?;
    if label != "<generatedTop>" {
        return Err("final configuration is not generatedTop".into());
    }
    let mut cells = BTreeMap::new();
    for cell in children {
        let (label, children) = application(cell)?;
        let child = children
            .first()
            .ok_or("configuration cell has no content")?;
        cells.insert(label, child);
    }
    if !matches!(cells.get("<k>").map(|term| term.unannotated()), Some(Term::Sequence(items)) if items.is_empty())
    {
        return Err("final k cell is not empty".into());
    }
    parse_map(
        cells
            .get("<env>")
            .ok_or("final configuration lacks env cell")?,
    )
}

pub(crate) fn search_frontier(term: &Term) -> Result<&Term, String> {
    let (label, arguments) = application(term)?;
    let [variable, frontier] = arguments else {
        return Err("expected one deterministic #Equals search solution".into());
    };
    if label != "#Equals" {
        return Err("expected one deterministic #Equals search solution".into());
    }
    if !matches!(variable.unannotated(), Term::Variable { name, .. } if name == "Result") {
        return Err("unexpected search result binder".into());
    }
    Ok(frontier)
}

fn sentence_kind(sentence: &Sentence) -> &'static str {
    match sentence {
        Sentence::SyntaxSort { .. } => "KSyntaxSort",
        Sentence::SortSynonym { .. } => "KSortSynonym",
        Sentence::SyntaxLexical { .. } => "KSyntaxLexical",
        Sentence::Production { .. } => "KProduction",
        Sentence::SyntaxAssociativity { .. } => "KSyntaxAssociativity",
        Sentence::SyntaxPriority { .. } => "KSyntaxPriority",
        Sentence::ContextAlias { .. } => "KContextAlias",
        Sentence::Context { .. } => "KContext",
        Sentence::Rule { .. } => "KRule",
        Sentence::Claim { .. } => "KClaim",
        Sentence::Configuration { .. } => "KConfiguration",
        Sentence::Bubble { .. } => "KBubble",
    }
}

fn sentence_fact(sentence: &Sentence) -> Result<Value, String> {
    let attributes = sentence.attributes();
    let klabel = match sentence {
        Sentence::Production { label, .. } => label.as_ref().map(|label| label.name.as_str()),
        _ => None,
    };
    Ok(json!({
        "sha256":format!("{:x}", Sha256::digest(super::canonical_json(&reader::sentence_value(sentence)?).as_bytes())),
        "node":sentence_kind(sentence),
        "label":attributes.get("label").unwrap_or(&Value::Null),
        "klabel":klabel,
        "attribute_keys":attributes.wire_entries().map(|(key,_)| key).collect::<Vec<_>>()
    }))
}

fn module_facts(document: &DefinitionDocument, name: &str) -> Result<Value, String> {
    let matches = document
        .definition
        .modules
        .iter()
        .enumerate()
        .filter(|(_, module)| module.name == name)
        .collect::<Vec<_>>();
    let [(module_index, module)] = matches.as_slice() else {
        return Err(format!(
            "expected one module {name:?}, found {}",
            matches.len()
        ));
    };
    let bad = document.bad_sentences.get(module_index);
    let total = module.local_sentences.len() + bad.map_or(0, BTreeMap::len);
    let mut sentences = module.local_sentences.iter();
    let mut counts = BTreeMap::<&str, usize>::new();
    let mut facts = Vec::with_capacity(total);
    for index in 0..total {
        if bad.is_some_and(|bad| bad.contains_key(&index)) {
            *counts.entry("badsentence").or_default() += 1;
            facts
                .push(json!({"node":"badsentence","label":null,"klabel":null,"attribute_keys":[],"sha256":format!("{:x}", Sha256::digest(super::canonical_json(&json!({"node":"badsentence"})).as_bytes()))}));
        } else {
            let sentence = sentences
                .next()
                .ok_or("invalid recorded sentence positions")?;
            *counts.entry(sentence_kind(sentence)).or_default() += 1;
            facts.push(sentence_fact(sentence)?);
        }
    }
    Ok(json!({"counts":counts,"sentences":facts}))
}

fn k_head(term: &Term, head: &str) -> Result<bool, String> {
    let (label, cells) = application(term)?;
    if label != "<generatedTop>" {
        return Err("configuration is not generatedTop".into());
    }
    let mut k = None;
    for cell in cells {
        let (label, contents) = application(cell)?;
        if label == "<k>" {
            k = contents.first();
        }
    }
    let Some(Term::Sequence(items)) = k.map(Term::unannotated) else {
        return Ok(false);
    };
    Ok(
        matches!(items.first().map(Term::unannotated),Some(Term::Apply { label,.. }) if label.name == head),
    )
}

pub(crate) fn handle(request: &Value, document: &Document) -> Result<Value, String> {
    let action = request
        .get("action")
        .and_then(Value::as_str)
        .ok_or("inspect requires action")?;
    match action {
        "envelope" => {
            if let Some(raw_policy) = request.get("policy") {
                let policy = serde_json::from_value(raw_policy.clone())
                    .map_err(|error| format!("invalid validation policy: {error}"))?;
                validate_term(document.term()?, &policy)?;
            }
            document.to_value()
        }
        "abstract_term" => {
            let names = serde_json::from_value(
                request
                    .get("label_map")
                    .cloned()
                    .ok_or("abstract_term requires label_map")?,
            )
            .map_err(|error| format!("invalid abstract label_map: {error}"))?;
            abstract_term(document.term()?, &names)
        }
        "module_facts" => {
            let wrapper;
            let definition = match document {
                Document::Definition(definition) => definition,
                Document::ModuleList {
                    main_module,
                    modules,
                } => {
                    wrapper = DefinitionDocument {
                        definition: Definition {
                            main_module: main_module.clone(),
                            modules: modules.clone(),
                            attributes: Attributes::default(),
                        },
                        bad_sentences: BTreeMap::new(),
                    };
                    &wrapper
                }
                Document::Term(_) => {
                    return Err("module_facts requires a definition or module list".into());
                }
            };
            if let Some(name) = request.get("name") {
                module_facts(
                    definition,
                    name.as_str().ok_or("module name must be a string")?,
                )
            } else {
                definition
                    .definition
                    .modules
                    .iter()
                    .map(|module| {
                        Ok((module.name.clone(), module_facts(definition, &module.name)?))
                    })
                    .collect::<Result<serde_json::Map<_, _>, String>>()
                    .map(Value::Object)
            }
        }
        "final_environment" => {
            let result = final_environment(document.term()?);
            if request.get("if_complete").and_then(Value::as_bool) == Some(true) {
                Ok(result.map_or(Value::Null, |environment| json!(environment)))
            } else {
                Ok(json!(result?))
            }
        }
        "search_frontier" => reader::term_value(search_frontier(document.term()?)?),
        "k_head" => {
            let head = request
                .get("head")
                .and_then(Value::as_str)
                .ok_or("k_head requires head")?;
            Ok(json!(k_head(document.term()?, head)?))
        }
        _ => Err(format!("unknown inspect action {action:?}")),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use k_rust::definition::{Attributes, Definition, FlatModule};

    use super::*;

    fn token(text: &str, sort: &str) -> Term {
        Term::Token {
            token: text.into(),
            sort: Sort::new(sort),
        }
    }

    fn map_entry(name: &str, value: &str) -> Term {
        Term::apply("_|->_", vec![token(name, "Id"), token(value, "Int")])
    }

    fn configuration(k: Term, env: Term) -> Term {
        Term::apply(
            "<generatedTop>",
            vec![Term::apply("<k>", vec![k]), Term::apply("<env>", vec![env])],
        )
    }

    #[test]
    fn concrete_environment_accepts_values_and_rejects_duplicate_keys() {
        assert_eq!(
            parse_map(&Term::apply(
                "_Map_",
                vec![map_entry("x", "1"), map_entry("y", "2")]
            ))
            .unwrap(),
            BTreeMap::from([("x".into(), "1".into()), ("y".into(), "2".into())])
        );
        assert!(
            parse_map(&Term::apply(
                "_Map_",
                vec![map_entry("x", "1"), map_entry("x", "2")]
            ))
            .is_err()
        );
        assert!(
            parse_map(&Term::apply(
                "_|->_",
                vec![token("x", "String"), token("1", "Int")]
            ))
            .is_err()
        );
        assert!(
            parse_map(&Term::apply(
                "_|->_",
                vec![token("x", "Id"), token("1", "String")]
            ))
            .is_err()
        );
    }

    #[test]
    fn final_environment_action_requires_completion_or_returns_null() {
        let document = Document::Term(configuration(Term::Sequence(vec![]), map_entry("x", "7")));
        assert_eq!(
            handle(&json!({"action":"final_environment"}), &document).unwrap(),
            json!({"x":"7"})
        );
        let document = Document::Term(configuration(
            Term::Sequence(vec![token("1", "Int")]),
            map_entry("x", "7"),
        ));
        assert!(handle(&json!({"action":"final_environment"}), &document).is_err());
        assert_eq!(
            handle(
                &json!({"action":"final_environment","if_complete":true}),
                &document
            )
            .unwrap(),
            Value::Null
        );
    }

    #[test]
    fn search_frontier_action_checks_binder_and_returns_a_term() {
        let result = Term::apply("state", vec![]);
        let document = Document::Term(Term::apply(
            "#Equals",
            vec![Term::variable("Result"), result.clone()],
        ));
        assert_eq!(
            handle(&json!({"action":"search_frontier"}), &document).unwrap(),
            reader::term_value(&result).unwrap()
        );
        assert!(
            search_frontier(&Term::apply(
                "#Equals",
                vec![Term::variable("Other"), result]
            ))
            .is_err()
        );
    }

    #[test]
    fn validators_close_labels_nodes_and_parameters() {
        let policy = TermValidationPolicy {
            labels: BTreeSet::from(["known".into()]),
            ..TermValidationPolicy::default()
        };
        assert!(validate_term(&Term::apply("known", vec![]), &policy).is_ok());
        assert!(validate_term(&Term::apply("unknown", vec![]), &policy).is_err());
        assert!(
            validate_label(
                &Label::with_parameters("known", vec![Sort::new("Int")]),
                &policy
            )
            .is_err()
        );
        assert!(validate_term(&Term::variable("X"), &policy).is_err());
        assert!(
            validate_sort(
                &Sort::with_parameters("Map", vec![Sort::new("Int")]),
                &policy
            )
            .is_err()
        );
    }

    #[test]
    fn envelope_action_validates_allowlists_and_returns_an_envelope() {
        let document = Document::Term(Term::apply("known", vec![]));
        let value = handle(
            &json!({"action":"envelope","policy":{"labels":["known"]}}),
            &document,
        )
        .unwrap();
        assert_eq!(value["format"], "KAST");
        assert_eq!(value["version"], k_rust::kast::json::VERSION);
        assert_eq!(
            value["term"],
            reader::term_value(document.term().unwrap()).unwrap()
        );
        assert!(
            handle(
                &json!({"action":"envelope","policy":{"labels":[]}}),
                &document
            )
            .is_err()
        );
    }

    #[test]
    fn abstraction_requires_an_explicit_mapping() {
        let document = Document::Term(Term::apply(
            "sum",
            vec![token("1", "Int"), token("2", "Int")],
        ));
        assert_eq!(
            handle(
                &json!({"action":"abstract_term","label_map":{"sum":"+"}}),
                &document
            )
            .unwrap(),
            json!(["+", ["Int", "1"], ["Int", "2"]])
        );
        assert!(handle(&json!({"action":"abstract_term","label_map":{}}), &document).is_err());
    }

    #[test]
    fn module_facts_retain_typed_attributes_and_fallback_positions() {
        let sentence = Sentence::Production {
            label: Some(Label::new("label")),
            parameters: vec![],
            sort: Sort::new("Int"),
            items: vec![],
            attributes: Attributes::new(BTreeMap::from([("strict".into(), json!("1"))])),
        };
        let module = FlatModule {
            name: "MAIN".into(),
            imports: vec![],
            local_sentences: vec![Arc::new(sentence)],
            attributes: Attributes::default(),
        };
        let document = Document::Definition(DefinitionDocument {
            definition: Definition {
                main_module: "MAIN".into(),
                modules: vec![module],
                attributes: Attributes::default(),
            },
            bad_sentences: BTreeMap::from([(
                0,
                BTreeMap::from([(0, json!({"node":"badsentence"}))]),
            )]),
        });
        let facts = handle(&json!({"action":"module_facts","name":"MAIN"}), &document).unwrap();
        assert_eq!(facts["counts"], json!({"badsentence":1,"KProduction":1}));
        assert_eq!(facts["sentences"][0]["node"], "badsentence");
        assert_eq!(facts["sentences"][1]["klabel"], "label");
        assert_eq!(facts["sentences"][1]["attribute_keys"], json!(["strict"]));
        assert!(
            handle(
                &json!({"action":"module_facts","name":"MISSING"}),
                &document
            )
            .is_err()
        );
    }

    #[test]
    fn k_head_checks_the_first_sequence_item() {
        let document = Document::Term(configuration(
            Term::Sequence(vec![Term::apply("selected", vec![])]),
            Term::apply(".Map", vec![]),
        ));
        assert_eq!(
            handle(&json!({"action":"k_head","head":"selected"}), &document).unwrap(),
            true
        );
        assert_eq!(
            handle(&json!({"action":"k_head","head":"other"}), &document).unwrap(),
            false
        );
        assert!(
            !k_head(
                &configuration(Term::Sequence(vec![]), Term::apply(".Map", vec![])),
                "selected"
            )
            .unwrap()
        );
    }
}
