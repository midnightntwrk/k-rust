use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::Path,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use k_rust::kore::{
    ast::{Attributes, Definition, Pattern, Sentence, Symbol},
    parser::parse_definition,
    parser::parse_pattern,
};
use k_rust::{
    definition::{
        json as definition_json,
        regex::{self, CharClass, RegexBody},
    },
    kast::json as kast_json,
};

#[test]
#[ignore = "requires K_REFERENCE_KORE and K_RUST_KORE outputs"]
fn emitted_kore_matches_the_reference_frontend() {
    let reference_path = env::var("K_REFERENCE_KORE").expect("K_REFERENCE_KORE is required");
    let actual_path = env::var("K_RUST_KORE").expect("K_RUST_KORE is required");
    let reference_source = fs::read_to_string(&reference_path).unwrap();
    let actual_source = fs::read_to_string(&actual_path).unwrap();
    let reference = parse_definition(&reference_source).unwrap();
    let actual = parse_definition(&actual_source).unwrap();
    compare_definitions(reference, actual);
}

#[test]
#[ignore = "requires K_REFERENCE_KORE and K_RUST_KORE outputs"]
fn emitted_macro_kore_matches_the_reference_frontend() {
    let reference_path = env::var("K_REFERENCE_KORE").expect("K_REFERENCE_KORE is required");
    let actual_path = env::var("K_RUST_KORE").expect("K_RUST_KORE is required");
    let reference_source = fs::read_to_string(&reference_path).unwrap();
    let actual_source = fs::read_to_string(&actual_path).unwrap();
    let reference = parse_macro_sentences(&reference_source);
    let actual = parse_macro_sentences(&actual_source);
    compare_definitions(reference, actual);
}

#[test]
#[ignore = "requires K_REFERENCE_KAST and K_RUST_KAST outputs"]
fn parsed_kast_matches_the_reference_frontend() {
    let reference_path = env::var("K_REFERENCE_KAST").expect("K_REFERENCE_KAST is required");
    let actual_path = env::var("K_RUST_KAST").expect("K_RUST_KAST is required");
    let reference_source = fs::read_to_string(&reference_path).unwrap();
    let actual_source = fs::read_to_string(&actual_path).unwrap();
    let reference = kast_json::from_str(&reference_source).unwrap();
    let actual = if let Ok(case) = env::var("K_RUST_KAST_CASE") {
        let batch: serde_json::Value = serde_json::from_str(&actual_source).unwrap();
        let encoded = serde_json::to_string(
            batch
                .get(&case)
                .unwrap_or_else(|| panic!("KAST batch output has no case {case:?}")),
        )
        .unwrap();
        kast_json::from_str(&encoded).unwrap()
    } else {
        kast_json::from_str(&actual_source).unwrap()
    };

    assert_eq!(reference, actual);
}

fn first_json_difference(
    path: &str,
    reference: &serde_json::Value,
    actual: &serde_json::Value,
) -> String {
    match (reference, actual) {
        (serde_json::Value::Object(reference), serde_json::Value::Object(actual)) => {
            let keys = reference
                .keys()
                .chain(actual.keys())
                .collect::<BTreeSet<_>>();
            for key in keys {
                match (reference.get(key), actual.get(key)) {
                    (Some(reference), Some(actual)) if reference != actual => {
                        return first_json_difference(&format!("{path}.{key}"), reference, actual);
                    }
                    (Some(_), None) => return format!("{path}.{key}: missing from actual"),
                    (None, Some(_)) => return format!("{path}.{key}: extra in actual"),
                    _ => {}
                }
            }
        }
        (serde_json::Value::Array(reference), serde_json::Value::Array(actual)) => {
            if reference.len() != actual.len() {
                return format!(
                    "{path}: array lengths differ: reference={} (first: {}), actual={} (first: {})",
                    reference.len(),
                    reference
                        .first()
                        .map(json_summary)
                        .unwrap_or_else(|| "<empty>".into()),
                    actual.len(),
                    actual
                        .first()
                        .map(json_summary)
                        .unwrap_or_else(|| "<empty>".into()),
                );
            }
            for (index, (reference, actual)) in reference.iter().zip(actual).enumerate() {
                if reference != actual {
                    return first_json_difference(&format!("{path}[{index}]"), reference, actual);
                }
            }
        }
        _ => {
            return format!("{path}: reference={reference:?}, actual={actual:?}");
        }
    }
    format!("{path}: values differ")
}

#[test]
#[ignore = "requires K_REFERENCE_DEFINITION and K_RUST_DEFINITION outputs"]
fn parsed_definition_matches_the_reference_frontend() {
    let reference_path =
        env::var("K_REFERENCE_DEFINITION").expect("K_REFERENCE_DEFINITION is required");
    let actual_path = env::var("K_RUST_DEFINITION").expect("K_RUST_DEFINITION is required");
    let reference_source = fs::read_to_string(reference_path).unwrap();
    let actual_source = fs::read_to_string(actual_path).unwrap();
    definition_json::from_str(&reference_source).unwrap();
    definition_json::from_str(&actual_source).unwrap();
    let mut reference: serde_json::Value = serde_json::from_str(&reference_source).unwrap();
    let mut actual: serde_json::Value = serde_json::from_str(&actual_source).unwrap();
    normalize_definition_json(&mut reference);
    normalize_definition_json(&mut actual);

    if reference != actual {
        if let Some(directory) = env::var_os("K_DIFFERENTIAL_NORMALIZED_DIRECTORY") {
            fs::create_dir_all(&directory).unwrap();
            fs::write(
                std::path::Path::new(&directory).join("reference.json"),
                serde_json::to_string_pretty(&reference).unwrap(),
            )
            .unwrap();
            fs::write(
                std::path::Path::new(&directory).join("actual.json"),
                serde_json::to_string_pretty(&actual).unwrap(),
            )
            .unwrap();
        }
        panic!(
            "normalized parsed definitions differ at {}",
            first_json_difference("$", &reference, &actual)
        );
    }
}

fn json_summary(value: &serde_json::Value) -> String {
    let text = json_sort_key(value);
    let mut summary = text.chars().take(400).collect::<String>();
    if summary.len() < text.len() {
        summary.push('…');
    }
    summary
}

fn normalize_definition_json(value: &mut serde_json::Value) {
    let associative_units = associative_units(value);
    normalize_definition_value(value, &associative_units);
    let modules = value["term"]["modules"]
        .as_array_mut()
        .expect("definition modules must be an array");
    for module in modules.iter_mut() {
        module["imports"]
            .as_array_mut()
            .expect("module imports must be an array")
            .sort_by_key(json_sort_key);
        let sentences = module["localSentences"]
            .as_array_mut()
            .expect("local sentences must be an array");
        let cell_sorts = sentences
            .iter()
            .filter(|sentence| {
                sentence["node"] == "KProduction" && sentence["att"]["att"].get("cell").is_some()
            })
            .filter_map(|sentence| sentence["sort"]["name"].as_str().map(str::to_owned))
            .collect::<BTreeSet<_>>();
        let mut normalized = Vec::new();
        for sentence in std::mem::take(sentences) {
            // Rust can retain an empty generated sort declaration alongside the cell production
            // that already declares that sort; Java's sentence set deduplicates it.
            let redundant_cell_sort = sentence["node"] == "KSyntaxSort"
                && sentence["att"]["att"]
                    .as_object()
                    .is_some_and(serde_json::Map::is_empty)
                && sentence["sort"]["name"]
                    .as_str()
                    .is_some_and(|sort| cell_sorts.contains(sort));
            if redundant_cell_sort {
                continue;
            } else if sentence["node"] == "KSyntaxAssociativity" {
                let tags = sentence["tags"]
                    .as_array()
                    .expect("associativity tags must be an array");
                for tag in tags {
                    let mut singleton = sentence.clone();
                    singleton["tags"] = serde_json::Value::Array(vec![tag.clone()]);
                    normalized.push(singleton);
                }
            } else {
                normalized.push(sentence);
            }
        }
        normalized.sort_by_key(json_sort_key);
        normalized.dedup();
        *sentences = normalized;
    }
    modules.sort_by_key(|module| module["name"].as_str().unwrap_or_default().to_owned());
}

fn associative_units(value: &serde_json::Value) -> BTreeMap<String, String> {
    fn collect(value: &serde_json::Value, result: &mut BTreeMap<String, String>) {
        match value {
            serde_json::Value::Array(values) => {
                for value in values {
                    collect(value, result);
                }
            }
            serde_json::Value::Object(object) => {
                if object.get("node").and_then(serde_json::Value::as_str) == Some("KProduction")
                    && object["att"]["att"].get("assoc").is_some()
                    && let (Some(label), Some(unit)) = (
                        object["klabel"]["name"].as_str(),
                        object["att"]["att"]["unit"].as_str(),
                    )
                {
                    result.insert(label.into(), unit.into());
                }
                if object.get("node").and_then(serde_json::Value::as_str) == Some("KProduction")
                    && object["att"]["att"].get("userList").is_some()
                    && object["productionItems"]
                        .as_array()
                        .is_some_and(|items| items.len() > 1)
                    && let (Some(label), Some(sort)) = (
                        object["klabel"]["name"].as_str(),
                        object["sort"]["name"].as_str(),
                    )
                {
                    result.insert(label.into(), format!(r#".List{{"{label}"}}_{sort}"#));
                }
                for value in object.values() {
                    collect(value, result);
                }
            }
            _ => {}
        }
    }

    let mut result = BTreeMap::new();
    collect(value, &mut result);
    result
}

fn normalize_definition_value(
    value: &mut serde_json::Value,
    associative_units: &BTreeMap<String, String>,
) {
    match value {
        serde_json::Value::Array(values) => {
            for value in values {
                normalize_definition_value(value, associative_units);
            }
        }
        serde_json::Value::Object(object) => {
            // These fields are frontend provenance or generated parser bookkeeping rather than
            // the parsed definition's semantic structure.
            for key in [
                "digest",
                "org.kframework.attributes.Source",
                "org.kframework.attributes.SourceId",
                "org.krust.provenance.Origin",
                "org.krust.provenance.SentenceStartOffset",
                "org.krust.provenance.SentenceEndOffset",
                "org.kframework.attributes.Location",
                "org.kframework.definition.Production",
                "contentStartColumn",
                "contentStartLine",
                "contentStartOffset",
                "temporary-cell-sort-decl",
            ] {
                object.remove(key);
            }
            if let Some(serde_json::Value::Object(label)) = object.get("bracketLabel")
                && let Some(name) = label.get("name").and_then(serde_json::Value::as_str)
            {
                object.insert("bracketLabel".into(), name.into());
            }
            for value in object.values_mut() {
                normalize_definition_value(value, associative_units);
            }
            match object.get("node").and_then(serde_json::Value::as_str) {
                Some("KVariable") => {
                    let Some(name) = object["name"].as_str() else {
                        return;
                    };
                    if name.starts_with('_') {
                        // Java HashSet traversal and deterministic Rust traversal allocate suffixes
                        // in different orders for generated anonymous variables.
                        let stem =
                            name.trim_end_matches(|character: char| character.is_ascii_digit());
                        if stem.len() != name.len() {
                            object.insert("name".into(), stem.into());
                        }
                    }
                }
                Some("KLabel") => {
                    // Java's parsed JSON omits inferred concrete label parameters; declarations
                    // still retain their separate `params` field, and KAST has its own exact gate.
                    object.insert("params".into(), serde_json::Value::Array(Vec::new()));
                }
                Some("KRegexTerminal") => {
                    let source = object["regex"].as_str().expect("regex must be a string");
                    let parsed = regex::parse(source).unwrap_or_else(|error| {
                        panic!("failed to normalize regex {source:?}: {error}")
                    });
                    object.insert(
                        "regex".into(),
                        canonical_regex(&parsed.body, parsed.start_line, parsed.end_line).into(),
                    );
                }
                Some("KSyntaxAssociativity") => {
                    object["tags"]
                        .as_array_mut()
                        .expect("associativity tags must be an array")
                        .sort_by_key(json_sort_key);
                }
                Some("KSyntaxPriority") => {
                    for group in object["priorities"]
                        .as_array_mut()
                        .expect("priority groups must be an array")
                    {
                        group
                            .as_array_mut()
                            .expect("priority group must be an array")
                            .sort_by_key(json_sort_key);
                    }
                }
                Some("KApply") => {
                    let Some(label) = object["label"]["name"].as_str() else {
                        return;
                    };
                    let Some(unit) = associative_units.get(label) else {
                        return;
                    };
                    let label = label.to_owned();
                    let arguments = object["args"]
                        .as_array_mut()
                        .expect("application arguments must be an array");
                    let mut flattened = Vec::new();
                    // User lists and associative productions can differ only in nesting and
                    // explicit unit insertion before both frontends lower them to identical KORE.
                    for argument in std::mem::take(arguments) {
                        let nested_label = argument["label"]["name"].as_str();
                        let nested_arguments = argument["args"].as_array();
                        if nested_label == Some(label.as_str()) {
                            flattened.extend(nested_arguments.unwrap().iter().cloned());
                        } else if nested_label == Some(unit.as_str())
                            && nested_arguments.is_some_and(Vec::is_empty)
                        {
                        } else {
                            flattened.push(argument);
                        }
                    }
                    if flattened.len() == 1
                        && let serde_json::Value::Object(singleton) = flattened.pop().unwrap()
                    {
                        *object = singleton;
                        return;
                    }
                    object.insert("arity".into(), flattened.len().into());
                    object.insert("args".into(), flattened.into());
                }
                _ => {}
            }
        }
        _ => {}
    }
}

fn json_sort_key(value: &serde_json::Value) -> String {
    match value {
        serde_json::Value::Array(values) => format!(
            "[{}]",
            values
                .iter()
                .map(json_sort_key)
                .collect::<Vec<_>>()
                .join(",")
        ),
        serde_json::Value::Object(object) => {
            let mut fields = object
                .iter()
                .map(|(key, value)| {
                    format!(
                        "{}:{}",
                        serde_json::to_string(key).unwrap(),
                        json_sort_key(value)
                    )
                })
                .collect::<Vec<_>>();
            fields.sort();
            format!("{{{}}}", fields.join(","))
        }
        value => serde_json::to_string(value).unwrap(),
    }
}

fn canonical_regex(body: &RegexBody, start_line: bool, end_line: bool) -> String {
    format!(
        "{}{}{}",
        if start_line { "^" } else { "" },
        canonical_regex_body(body),
        if end_line { "$" } else { "" },
    )
}

fn canonical_regex_body(body: &RegexBody) -> String {
    match body {
        RegexBody::Char(character) => format!("char:{character:?}"),
        RegexBody::AnyChar => "any".into(),
        RegexBody::Named(name) => format!("named:{name}"),
        RegexBody::CharClass { negated, members } => {
            let mut members = members
                .iter()
                .map(|member| match member {
                    CharClass::Char(character) => format!("char:{character:?}"),
                    CharClass::Range { start, end } => format!("range:{start:?}:{end:?}"),
                })
                .collect::<Vec<_>>();
            members.sort();
            members.dedup();
            format!("class:{negated}:[{}]", members.join(","))
        }
        RegexBody::Union { .. } => {
            fn flatten(body: &RegexBody, members: &mut Vec<String>) {
                if let RegexBody::Union { left, right } = body {
                    flatten(left, members);
                    flatten(right, members);
                } else {
                    members.push(canonical_regex_body(body));
                }
            }
            let mut members = Vec::new();
            flatten(body, &mut members);
            members.sort();
            members.dedup();
            format!("union:[{}]", members.join(","))
        }
        RegexBody::Concat(members) => format!(
            "concat:[{}]",
            members
                .iter()
                .map(canonical_regex_body)
                .collect::<Vec<_>>()
                .join(",")
        ),
        RegexBody::ZeroOrMore(body) => format!("star:{}", canonical_regex_body(body)),
        RegexBody::ZeroOrOne(body) => format!("optional:{}", canonical_regex_body(body)),
        RegexBody::OneOrMore(body) => format!("plus:{}", canonical_regex_body(body)),
        RegexBody::Exactly { body, count } => {
            format!("exactly:{count}:{}", canonical_regex_body(body))
        }
        RegexBody::AtLeast { body, count } => {
            format!("at-least:{count}:{}", canonical_regex_body(body))
        }
        RegexBody::Range {
            body,
            at_least,
            at_most,
        } => format!("range:{at_least}:{at_most}:{}", canonical_regex_body(body)),
    }
}

#[test]
fn definition_normalizer_compares_regex_languages() {
    let left = regex::parse("[A-Za-z_]").unwrap();
    let right = regex::parse(r"[A-Za-z\_]").unwrap();

    assert_eq!(
        canonical_regex(&left.body, left.start_line, left.end_line),
        canonical_regex(&right.body, right.start_line, right.end_line),
    );
}

#[test]
fn definition_normalizer_flattens_user_lists_and_generated_variables() {
    let mut reference = serde_json::json!({
        "node": "KApply",
        "label": { "node": "KLabel", "name": "cons", "params": [{ "name": "Items" }] },
        "arity": 2,
        "args": [
            {
                "node": "KApply",
                "label": { "node": "KLabel", "name": "cast", "params": [] },
                "arity": 1,
                "args": [{ "node": "KVariable", "name": "_item1" }]
            },
            {
                "node": "KApply",
                "label": { "node": "KLabel", "name": ".Items", "params": [] },
                "arity": 0,
                "args": []
            }
        ]
    });
    let mut actual = serde_json::json!({
        "node": "KApply",
        "label": { "node": "KLabel", "name": "cast", "params": [{ "name": "Items" }] },
        "arity": 1,
        "args": [{ "node": "KVariable", "name": "_item7" }]
    });
    let units = BTreeMap::from([("cons".into(), ".Items".into())]);

    normalize_definition_value(&mut reference, &units);
    normalize_definition_value(&mut actual, &units);

    assert_eq!(reference, actual);
}

#[test]
fn definition_normalizer_canonicalizes_set_valued_outer_syntax() {
    let associativity = |tags: serde_json::Value| {
        serde_json::json!({
            "node": "KSyntaxAssociativity",
            "assoc": "Left",
            "tags": tags,
            "att": { "node": "KAtt", "att": {} }
        })
    };
    let priority = |first: serde_json::Value| {
        serde_json::json!({
            "node": "KSyntaxPriority",
            "priorities": [first, ["low"]],
            "att": { "node": "KAtt", "att": {} }
        })
    };
    let module = |imports: serde_json::Value, sentences: serde_json::Value| {
        serde_json::json!({
            "node": "KFlatModule",
            "name": "A",
            "imports": imports,
            "localSentences": sentences,
            "att": { "node": "KAtt", "att": {} }
        })
    };
    let empty_module = serde_json::json!({
        "node": "KFlatModule",
        "name": "B",
        "imports": [],
        "localSentences": [],
        "att": { "node": "KAtt", "att": {} }
    });
    let import_y = serde_json::json!({ "node": "KImport", "name": "Y", "isPublic": true });
    let import_z = serde_json::json!({ "node": "KImport", "name": "Z", "isPublic": true });
    let mut reference = serde_json::json!({
        "term": {
            "modules": [
                empty_module.clone(),
                module(
                    serde_json::json!([import_z.clone(), import_y.clone()]),
                    serde_json::json!([
                        associativity(serde_json::json!(["right", "left"])),
                        priority(serde_json::json!(["right", "left"]))
                    ])
                )
            ]
        }
    });
    let mut actual = serde_json::json!({
        "term": {
            "modules": [
                module(
                    serde_json::json!([import_y, import_z]),
                    serde_json::json!([
                        priority(serde_json::json!(["left", "right"])),
                        associativity(serde_json::json!(["left"])),
                        associativity(serde_json::json!(["right"]))
                    ])
                ),
                empty_module
            ]
        }
    });

    normalize_definition_json(&mut reference);
    normalize_definition_json(&mut actual);

    assert_eq!(reference, actual);
}

#[test]
#[ignore = "requires K_REFERENCE_EXECUTION and K_RUST_EXECUTION outputs"]
fn executed_kore_matches_the_reference_backend() {
    let reference_path =
        env::var("K_REFERENCE_EXECUTION").expect("K_REFERENCE_EXECUTION is required");
    let actual_path = env::var("K_RUST_EXECUTION").expect("K_RUST_EXECUTION is required");
    let reference_source = fs::read_to_string(&reference_path).unwrap();
    let actual_source = fs::read_to_string(&actual_path).unwrap();
    let reference = normalize_execution_pattern(parse_pattern(&reference_source).unwrap());
    let actual = normalize_execution_pattern(parse_pattern(&actual_source).unwrap());

    let definition = env::var_os("K_DIFFERENTIAL_DEFINITION");
    let module = env::var("K_DIFFERENTIAL_MODULE").unwrap_or_else(|_| "MAIN".into());
    let definition = definition.as_deref().map(Path::new);
    let result = match env::var("K_DIFFERENTIAL_ORACLE_EXCLUSION").as_deref() {
        Ok("gotstuck") => {
            let stop_path = env::var("K_DIFFERENTIAL_STOP_LEAVES")
                .expect("K_DIFFERENTIAL_STOP_LEAVES is required for the gotstuck exclusion");
            let stop_source = fs::read_to_string(stop_path).unwrap();
            let stop_leaves = normalize_execution_pattern(parse_pattern(&stop_source).unwrap());
            compare_execution_modulo_gotstuck(
                &reference,
                &actual,
                &stop_leaves,
                definition,
                &module,
            )
        }
        Ok(exclusion) => Err(format!("unknown oracle exclusion: {exclusion}")),
        Err(_) => compare_execution_modulo_implication(&reference, &actual, definition, &module),
    };
    result.unwrap_or_else(|error| panic!("{error}"));
}

#[test]
fn execution_normalizer_treats_search_disjunctions_as_result_sets() {
    let left = parse_pattern(r"\or{S{}}(\or{S{}}(a{}(), b{}()), c{}())").unwrap();
    let right = parse_pattern(r"\or{S{}}(\or{S{}}(c{}(), a{}()), b{}())").unwrap();
    assert_eq!(
        normalize_execution_pattern(left),
        normalize_execution_pattern(right)
    );
}

#[test]
fn execution_normalizer_reassociates_map_concatenation() {
    let left =
        parse_pattern(r"Lbl'Unds'Map'Unds'{}(Lbl'Unds'Map'Unds'{}(a{}(), b{}()), c{}())").unwrap();
    let right =
        parse_pattern(r"Lbl'Unds'Map'Unds'{}(c{}(), Lbl'Unds'Map'Unds'{}(b{}(), a{}()))").unwrap();

    assert_eq!(
        normalize_execution_pattern(left),
        normalize_execution_pattern(right)
    );
}

#[test]
fn execution_normalizer_keeps_different_sort_disjunctions_nested() {
    let nested = parse_pattern(r"\or{S{}}(\or{T{}}(a{}(), b{}()), c{}())").unwrap();
    let flattened = parse_pattern(r"\or{S{}}(a{}(), \or{T{}}(b{}(), c{}()))").unwrap();

    assert_ne!(
        normalize_execution_pattern(nested),
        normalize_execution_pattern(flattened)
    );
}

#[test]
fn execution_normalizer_preserves_disjunction_multiplicity() {
    let repeated = parse_pattern(r"\or{S{}}(a{}(), a{}(), b{}())").unwrap();
    let unique = parse_pattern(r"\or{S{}}(a{}(), b{}())").unwrap();

    assert_ne!(
        normalize_execution_pattern(repeated),
        normalize_execution_pattern(unique)
    );
}

#[test]
fn execution_normalizer_drops_the_outer_existential_prefix() {
    let quantified =
        parse_pattern(r"\exists{S{}}(Var'Unds'AC1:S{}, \and{S{}}(a{}(), Var'Unds'AC1:S{}))")
            .unwrap();
    let body = parse_pattern(r"\and{S{}}(a{}(), Var'Unds'AC7:S{})").unwrap();

    assert_eq!(
        normalize_execution_pattern(quantified),
        normalize_execution_pattern(body)
    );
}

#[test]
fn execution_normalizer_emits_reparseable_generated_variable_names() {
    let pattern = parse_pattern(
        r"\and{S{}}(f{}(Var'Unds'X1:S{}, Var'Unds'X2:S{}), \equals{S{}, S{}}(Var'Unds'X1:S{}, Var'Unds'X2:S{}))",
    )
    .unwrap();
    let normalized = normalize_execution_pattern(pattern);
    let rendered = normalized.to_string();

    parse_pattern(&rendered)
        .unwrap_or_else(|error| panic!("normalized KORE must reparse ({error}): {rendered}"));
}

#[test]
fn execution_comparator_pairs_disjuncts_by_term_and_reports_unpaired() {
    let reference =
        normalize_execution_pattern(parse_pattern(r"\and{S{}}(a{}(), \top{S{}}())").unwrap());
    let different_constraints =
        normalize_execution_pattern(parse_pattern(r"\and{S{}}(a{}(), \bottom{S{}}())").unwrap());
    let error =
        compare_execution_modulo_implication(&reference, &different_constraints, None, "TEST")
            .expect_err("different constraints need an implication definition");
    assert!(error.contains("constraints differ"), "{error}");

    let different_term = normalize_execution_pattern(parse_pattern("b{}()").unwrap());
    let error = compare_execution_modulo_implication(&reference, &different_term, None, "TEST")
        .expect_err("different terms cannot be paired");
    assert!(error.contains("unpaired disjunct"), "{error}");
}

#[test]
fn execution_comparator_allows_only_marked_gotstuck_stop_leaves() {
    let reference = normalize_execution_pattern(parse_pattern("a{}()").unwrap());
    let actual = normalize_execution_pattern(parse_pattern(r"\or{S{}}(a{}(), b{}())").unwrap());
    let stop_leaves = normalize_execution_pattern(parse_pattern("b{}()").unwrap());
    compare_execution_modulo_gotstuck(&reference, &actual, &stop_leaves, None, "TEST")
        .expect("the one extra actual leaf is marked as depth-bounded");

    let wrong_stop = normalize_execution_pattern(parse_pattern("c{}()").unwrap());
    let error = compare_execution_modulo_gotstuck(&reference, &actual, &wrong_stop, None, "TEST")
        .expect_err("an unmarked actual leaf must still fail");
    assert!(error.contains("unpaired disjunct"), "{error}");
}

#[test]
fn implication_fallback_checks_both_directions_and_requires_valid() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = env::temp_dir().join(format!(
        "k-rust-implication-fake-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&directory).unwrap();
    let calls = directory.join("calls");
    let valid = directory.join("valid-krust");
    let invalid = directory.join("invalid-krust");
    fs::write(
        &valid,
        format!(
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >>{}\nprintf '{{\"status\":\"valid\"}}\\n'\n",
            calls.display()
        ),
    )
    .unwrap();
    fs::write(
        &invalid,
        "#!/usr/bin/env bash\nprintf '{\"status\":\"indeterminate\"}\\n'\n",
    )
    .unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        for path in [&valid, &invalid] {
            let mut permissions = fs::metadata(path).unwrap().permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(path, permissions).unwrap();
        }
    }
    let reference = normalize_execution_pattern(
        parse_pattern(r"\and{S{}}(f{}(Var'Unds'X1:S{}), \top{S{}}())").unwrap(),
    );
    let actual = normalize_execution_pattern(
        parse_pattern(
            r"\and{S{}}(f{}(Var'Unds'X9:S{}), \equals{S{}, S{}}(Var'Unds'X9:S{}, Var'Unds'X9:S{}))",
        )
        .unwrap(),
    );
    let definition = directory.join("definition.kore");
    fs::write(&definition, "[]").unwrap();

    prove_implication_both_ways_with(&valid, &reference, &actual, &definition, "TEST")
        .expect("both valid directions");
    let calls = fs::read_to_string(&calls).unwrap();
    assert_eq!(calls.lines().count(), 2, "both implication directions");
    assert!(calls.lines().all(|line| line.contains("--module TEST")));
    assert!(
        calls
            .lines()
            .all(|line| line.contains(definition.to_str().unwrap()))
    );

    let error =
        prove_implication_both_ways_with(&invalid, &reference, &actual, &definition, "TEST")
            .expect_err("an indeterminate answer cannot certify equivalence");
    assert!(error.contains("not valid"), "{error}");
    fs::remove_dir_all(directory).unwrap();
}

fn normalize_execution_pattern(pattern: Pattern) -> Pattern {
    let pattern = normalize_execution_structure(pattern);
    match &pattern {
        Pattern::Or { sort, arguments } => Pattern::Or {
            sort: sort.clone(),
            // D1-06 / arbiter row 12: disjunction order is semantically empty, so execution
            // gates compare a sorted multiset. C3-02 requires retaining multiplicity here:
            // duplicate final configurations are a backend defect, not a gate normalization.
            arguments: arguments
                .iter()
                .cloned()
                .map(normalize_execution_disjunct)
                .collect(),
        },
        _ => normalize_execution_disjunct(pattern),
    }
}

fn normalize_execution_disjunct(mut pattern: Pattern) -> Pattern {
    // N16: reference execution can leave an AC remainder variable free while
    // the port quantifies its corresponding generated variable.
    while let Pattern::Exists { body, .. } = &mut pattern {
        pattern = std::mem::replace(body.as_mut(), Pattern::String(String::new()));
    }
    rename_generated_variables(&mut pattern);
    pattern
}

fn normalize_execution_structure(pattern: Pattern) -> Pattern {
    match &pattern {
        Pattern::Application { symbol, arguments } => {
            let arguments = arguments
                .iter()
                .cloned()
                .map(normalize_execution_structure)
                .collect::<Vec<_>>();
            if matches!(
                symbol.name.as_str(),
                "Lbl'Unds'Map'Unds'" | "Lbl'Unds'Set'Unds'"
            ) {
                let mut flattened = Vec::new();
                for argument in arguments {
                    flatten_collection(&symbol, argument, &mut flattened);
                }
                flattened.sort();
                let mut flattened = flattened.into_iter().rev();
                let mut result = flattened
                    .next()
                    .expect("collection concatenation is binary");
                for argument in flattened {
                    result = Pattern::Application {
                        symbol: symbol.clone(),
                        arguments: vec![argument, result],
                    };
                }
                result
            } else {
                Pattern::Application {
                    symbol: symbol.clone(),
                    arguments,
                }
            }
        }
        Pattern::And { sort, arguments } => Pattern::And {
            sort: sort.clone(),
            arguments: arguments
                .iter()
                .cloned()
                .map(normalize_execution_structure)
                .collect(),
        },
        Pattern::Or { sort, arguments } => {
            let mut flattened = Vec::new();
            for mut argument in arguments.iter().cloned().map(normalize_execution_structure) {
                let nested = match &mut argument {
                    Pattern::Or {
                        sort: nested_sort,
                        arguments,
                    } if nested_sort == sort => Some(std::mem::take(arguments)),
                    _ => None,
                };
                if let Some(mut nested) = nested {
                    flattened.append(&mut nested);
                } else {
                    flattened.push(argument);
                }
            }
            flattened.sort();
            Pattern::Or {
                sort: sort.clone(),
                arguments: flattened,
            }
        }
        Pattern::Not { sort, argument } => Pattern::Not {
            sort: sort.clone(),
            argument: Box::new(normalize_execution_structure((**argument).clone())),
        },
        Pattern::Next { sort, argument } => Pattern::Next {
            sort: sort.clone(),
            argument: Box::new(normalize_execution_structure((**argument).clone())),
        },
        Pattern::Implies { sort, left, right } => Pattern::Implies {
            sort: sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::Iff { sort, left, right } => Pattern::Iff {
            sort: sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::Rewrites { sort, left, right } => Pattern::Rewrites {
            sort: sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::Exists {
            sort,
            variable,
            body,
        } => Pattern::Exists {
            sort: sort.clone(),
            variable: variable.clone(),
            body: Box::new(normalize_execution_structure((**body).clone())),
        },
        Pattern::Forall {
            sort,
            variable,
            body,
        } => Pattern::Forall {
            sort: sort.clone(),
            variable: variable.clone(),
            body: Box::new(normalize_execution_structure((**body).clone())),
        },
        Pattern::Mu { variable, body } => Pattern::Mu {
            variable: variable.clone(),
            body: Box::new(normalize_execution_structure((**body).clone())),
        },
        Pattern::Nu { variable, body } => Pattern::Nu {
            variable: variable.clone(),
            body: Box::new(normalize_execution_structure((**body).clone())),
        },
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => Pattern::Ceil {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: Box::new(normalize_execution_structure((**argument).clone())),
        },
        Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => Pattern::Floor {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: Box::new(normalize_execution_structure((**argument).clone())),
        },
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => Pattern::Equals {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => Pattern::In {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => Pattern::AssociativeApplication {
            associativity: *associativity,
            symbol: symbol.clone(),
            arguments: arguments
                .iter()
                .cloned()
                .map(normalize_execution_structure)
                .collect(),
        },
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => pattern,
    }
}

fn flatten_collection(symbol: &Symbol, mut pattern: Pattern, output: &mut Vec<Pattern>) {
    let nested_arguments = match &mut pattern {
        Pattern::Application {
            symbol: nested,
            arguments,
        } if *nested == *symbol => Some(std::mem::take(arguments)),
        _ => None,
    };
    if let Some(arguments) = nested_arguments {
        for argument in arguments {
            flatten_collection(symbol, argument, output);
        }
    } else {
        output.push(pattern);
    }
}

fn compare_execution_modulo_implication(
    reference: &Pattern,
    actual: &Pattern,
    definition: Option<&Path>,
    module: &str,
) -> Result<(), String> {
    compare_execution_disjuncts(reference, actual, definition, module, None)
}

fn compare_execution_modulo_gotstuck(
    reference: &Pattern,
    actual: &Pattern,
    stop_leaves: &Pattern,
    definition: Option<&Path>,
    module: &str,
) -> Result<(), String> {
    compare_execution_disjuncts(reference, actual, definition, module, Some(stop_leaves))
}

fn compare_execution_disjuncts(
    reference: &Pattern,
    actual: &Pattern,
    definition: Option<&Path>,
    module: &str,
    expected_unpaired_actual: Option<&Pattern>,
) -> Result<(), String> {
    if reference == actual {
        return match expected_unpaired_actual {
            Some(stop_leaves) if !is_empty_disjunction(stop_leaves) => Err(
                "oracle exception no longer needed: no GotStuck leaves are missing from the reference"
                    .into(),
            ),
            _ => Ok(()),
        };
    }

    let reference_disjuncts = execution_disjuncts(reference);
    let actual_disjuncts = execution_disjuncts(actual);
    let mut paired_actual = vec![false; actual_disjuncts.len()];
    for reference_disjunct in reference_disjuncts {
        let (reference_term, mut reference_constraints) = split_constrained(reference_disjunct);
        let Some((actual_index, actual_disjunct)) =
            actual_disjuncts
                .iter()
                .enumerate()
                .find(|(index, actual_disjunct)| {
                    !paired_actual[*index] && split_constrained(actual_disjunct).0 == reference_term
                })
        else {
            return Err(format!("unpaired disjunct: {reference_term}"));
        };
        paired_actual[actual_index] = true;
        let (_, mut actual_constraints) = split_constrained(actual_disjunct);
        reference_constraints.sort();
        actual_constraints.sort();
        if reference_constraints == actual_constraints {
            continue;
        }
        let Some(definition) = definition else {
            return Err(format!(
                "constraints differ for paired disjunct {reference_term}; K_DIFFERENTIAL_DEFINITION is not set"
            ));
        };
        prove_implication_both_ways(reference_disjunct, actual_disjunct, definition, module)?;
    }
    let unpaired_actual = paired_actual
        .iter()
        .enumerate()
        .filter(|(_, paired)| !**paired)
        .map(|(index, _)| actual_disjuncts[index])
        .collect::<Vec<_>>();
    if let Some(expected) = expected_unpaired_actual {
        let mut expected = execution_disjuncts(expected)
            .into_iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let mut unpaired = unpaired_actual
            .iter()
            .map(|pattern| pattern.to_string())
            .collect::<Vec<_>>();
        expected.sort();
        unpaired.sort();
        if unpaired != expected {
            let term = unpaired_actual
                .first()
                .map(|pattern| split_constrained(pattern).0.to_string())
                .unwrap_or_else(|| "<none>".into());
            return Err(format!(
                "unpaired disjunct: {term}; GotStuck stop leaves differ (expected {expected:?}, actual {unpaired:?})"
            ));
        }
    } else if let Some(disjunct) = unpaired_actual.first() {
        let (term, _) = split_constrained(disjunct);
        return Err(format!("unpaired disjunct: {term}"));
    }
    Ok(())
}

fn is_empty_disjunction(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Or { arguments, .. } if arguments.is_empty())
}

fn execution_disjuncts(pattern: &Pattern) -> Vec<&Pattern> {
    match pattern {
        Pattern::Or { arguments, .. } => arguments.iter().collect(),
        pattern => vec![pattern],
    }
}

fn split_constrained(pattern: &Pattern) -> (&Pattern, Vec<Pattern>) {
    let Pattern::And { arguments, .. } = pattern else {
        return (pattern, Vec::new());
    };
    let terms = arguments
        .iter()
        .enumerate()
        .filter(|(_, argument)| !is_predicate_pattern(argument))
        .collect::<Vec<_>>();
    let [(term_index, term)] = terms.as_slice() else {
        return (pattern, Vec::new());
    };
    let constraints = arguments
        .iter()
        .enumerate()
        .filter(|(index, _)| index != term_index)
        .map(|(_, argument)| argument.clone())
        .collect();
    (term, constraints)
}

fn is_predicate_pattern(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::Ceil { .. }
        | Pattern::Floor { .. }
        | Pattern::Equals { .. }
        | Pattern::In { .. } => true,
        Pattern::Not { argument, .. } => is_predicate_pattern(argument),
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            arguments.iter().all(is_predicate_pattern)
        }
        _ => false,
    }
}

fn prove_implication_both_ways(
    reference: &Pattern,
    actual: &Pattern,
    definition: &Path,
    module: &str,
) -> Result<(), String> {
    let krust = env::var_os("K_RUST_KRUST")
        .map(std::path::PathBuf::from)
        .or_else(|| option_env!("CARGO_BIN_EXE_krust").map(std::path::PathBuf::from))
        .unwrap_or_else(|| std::path::PathBuf::from("target/release/krust"));
    prove_implication_both_ways_with(&krust, reference, actual, definition, module)
}

fn prove_implication_both_ways_with(
    krust: &Path,
    reference: &Pattern,
    actual: &Pattern,
    definition: &Path,
    module: &str,
) -> Result<(), String> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| format!("system clock before Unix epoch: {error}"))?
        .as_nanos();
    let directory = env::temp_dir().join(format!(
        "k-rust-execution-implication-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&directory).map_err(|error| format!("create implication fixture: {error}"))?;
    let reference_path = directory.join("reference.kore");
    let actual_path = directory.join("actual.kore");
    fs::write(&reference_path, reference.to_string())
        .map_err(|error| format!("write reference implication pattern: {error}"))?;
    fs::write(&actual_path, actual.to_string())
        .map_err(|error| format!("write actual implication pattern: {error}"))?;

    let result = (|| {
        prove_implication(
            krust,
            &reference_path,
            &actual_path,
            definition,
            module,
            "reference => actual",
        )?;
        prove_implication(
            krust,
            &actual_path,
            &reference_path,
            definition,
            module,
            "actual => reference",
        )
    })();
    let _ = fs::remove_dir_all(directory);
    result
}

fn prove_implication(
    krust: &Path,
    antecedent: &Path,
    consequent: &Path,
    definition: &Path,
    module: &str,
    direction: &str,
) -> Result<(), String> {
    let output = Command::new(krust)
        .arg("kore-implies")
        .arg(definition)
        .arg("--module")
        .arg(module)
        .arg("--antecedent")
        .arg(antecedent)
        .arg("--consequent")
        .arg(consequent)
        .output()
        .map_err(|error| format!("run {} for {direction}: {error}", krust.display()))?;
    if !output.status.success() {
        return Err(format!(
            "constraint implication {direction} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let response: serde_json::Value = serde_json::from_slice(&output.stdout).map_err(|error| {
        format!(
            "constraint implication {direction} returned invalid JSON ({error}): {}",
            String::from_utf8_lossy(&output.stdout)
        )
    })?;
    if response["status"] != "valid" {
        return Err(format!(
            "constraint implication {direction} is not valid: {response}"
        ));
    }
    Ok(())
}

fn parse_macro_sentences(source: &str) -> Definition {
    parse_definition(&format!("[]\nmodule MACROS\n{source}\nendmodule []\n"))
        .expect("macro sentence list should parse")
}

#[test]
fn comparator_ignores_generated_variable_suffixes() {
    let reference = differential_definition("axiom{} Var'Unds'Gen7:S{} []");
    let actual = differential_definition("axiom{} Var'Unds'Gen9:S{} []");

    compare_definitions(reference, actual);
}

#[test]
fn comparator_detects_unique_id_differences_by_default() {
    let reference = differential_definition(r#"axiom{} a{}() [UNIQUE'Unds'ID{}("reference-id")]"#);
    let actual = differential_definition(r#"axiom{} a{}() [UNIQUE'Unds'ID{}("actual-id")]"#);

    assert!(
        std::panic::catch_unwind(|| compare_definitions(reference, actual)).is_err(),
        "UNIQUE_ID must participate in the default differential comparison"
    );
}

#[test]
fn comparator_skips_ids_of_multi_alias_freezer_axioms() {
    let definition = |first_id: &str, second_id: &str| {
        parse_definition(&format!(
            r#"[]
            module TEST
              sort S{{}} []
              symbol Lbl'Hash'freezerfoo'Unds'0{{}}() : S{{}} []
              symbol Lbl'Hash'freezerfoo'Unds'1{{}}() : S{{}} []
              axiom{{}} Lbl'Hash'freezerfoo'Unds'0{{}}() [UNIQUE'Unds'ID{{}}("{first_id}")]
              axiom{{}} Lbl'Hash'freezerfoo'Unds'1{{}}() [UNIQUE'Unds'ID{{}}("{second_id}")]
            endmodule []"#,
        ))
        .unwrap()
    };

    compare_definitions(
        definition("reference-zero", "reference-one"),
        definition("actual-zero", "actual-one"),
    );
}

#[test]
fn comparator_keeps_distinct_generated_variables_distinct() {
    let distinct =
        differential_definition(r"axiom{} \and{S{}}(Var'Unds'X1:S{}, Var'Unds'X2:S{}) []");
    let repeated =
        differential_definition(r"axiom{} \and{S{}}(Var'Unds'X1:S{}, Var'Unds'X1:S{}) []");

    assert!(
        std::panic::catch_unwind(|| compare_definitions(distinct, repeated)).is_err(),
        "two generated variables must not compare equal to one repeated variable"
    );

    let reference =
        differential_definition(r"axiom{} \and{S{}}(Var'Unds'X1:S{}, Var'Unds'X2:S{}) []");
    let actual = differential_definition(r"axiom{} \and{S{}}(Var'Unds'X7:S{}, Var'Unds'X9:S{}) []");
    compare_definitions(reference, actual);
}

#[test]
fn comparator_treats_same_sort_disjunction_order_as_equal() {
    let reference = differential_definition(r"axiom{} \or{S{}}(a{}(), b{}(), c{}()) []");
    let actual = differential_definition(r"axiom{} \or{S{}}(\or{S{}}(c{}(), a{}()), b{}()) []");

    compare_definitions(reference, actual);
}

#[test]
fn comparator_reorders_existential_binder_chains() {
    let reference = differential_definition(
        r"axiom{} \exists{S{}}(X:S{}, \exists{S{}}(Y:S{}, \and{S{}}(X:S{}, Y:S{}))) []",
    );
    let actual = differential_definition(
        r"axiom{} \exists{S{}}(Y:S{}, \exists{S{}}(X:S{}, \and{S{}}(X:S{}, Y:S{}))) []",
    );

    compare_definitions(reference, actual);
}

#[test]
fn comparator_reorders_universal_binder_chains() {
    let reference = differential_definition(
        r"axiom{} \forall{S{}}(X:S{}, \forall{S{}}(Y:S{}, \and{S{}}(X:S{}, Y:S{}))) []",
    );
    let actual = differential_definition(
        r"axiom{} \forall{S{}}(Y:S{}, \forall{S{}}(X:S{}, \and{S{}}(X:S{}, Y:S{}))) []",
    );

    compare_definitions(reference, actual);
}

#[test]
fn comparator_alpha_normalizes_disjoint_bound_variable_names() {
    let reference = differential_definition(
        r"axiom{} \or{S{}}(
            \exists{S{}}(X:S{}, X:S{}),
            \exists{S{}}(X:T{}, X:T{})
        ) []",
    );
    let actual = differential_definition(
        r"axiom{} \or{S{}}(
            \exists{S{}}(X:S{}, X:S{}),
            \exists{S{}}(X0V2:T{}, X0V2:T{})
        ) []",
    );

    compare_definitions(reference, actual);
}

#[test]
fn comparator_detects_multiplicity_differences() {
    let reference = differential_definition("axiom{} a{}() []\naxiom{} a{}() []");
    let actual = differential_definition("axiom{} a{}() []");

    assert!(
        std::panic::catch_unwind(|| compare_definitions(reference, actual)).is_err(),
        "the comparator must retain sentence multiplicity"
    );
}

#[test]
fn comparator_reports_the_first_differing_sentence() {
    let reference = differential_definition(
        r#"axiom{} a{}() [UNIQUE'Unds'ID{}("common")]
           axiom{} b{}() [UNIQUE'Unds'ID{}("expected-second")]"#,
    );
    let actual = differential_definition(
        r#"axiom{} a{}() [UNIQUE'Unds'ID{}("common")]
           axiom{} c{}() [UNIQUE'Unds'ID{}("actual-second")]"#,
    );

    let panic = std::panic::catch_unwind(|| compare_definitions(reference, actual))
        .expect_err("different sentences must fail comparison");
    let message = panic_message(panic);
    assert!(message.contains("first differing sentence=5"), "{message}");
    assert!(message.contains("expected-second"), "{message}");
    assert!(message.contains("actual-second"), "{message}");
}

fn differential_definition(sentences: &str) -> Definition {
    parse_definition(&format!(
        r#"[]
        module TEST
          sort S{{}} []
          symbol a{{}}() : S{{}} []
          symbol b{{}}() : S{{}} []
          symbol c{{}}() : S{{}} []
          {sentences}
        endmodule []"#
    ))
    .expect("differential test definition should parse")
}

fn panic_message(panic: Box<dyn std::any::Any + Send>) -> String {
    match panic.downcast::<String>() {
        Ok(message) => *message,
        Err(panic) => panic
            .downcast::<&'static str>()
            .map(|message| (*message).to_owned())
            .unwrap_or_else(|_| "non-string panic".into()),
    }
}

#[derive(Clone, Copy, Debug)]
struct CompareOptions {
    skip_multi_alias_ids: bool,
}

impl Default for CompareOptions {
    fn default() -> Self {
        Self {
            // Decisions 07-1 and 13-3: freezer suffixes for multi-alias context groups
            // follow Scala HashSet iteration in the oracle. Keep the port's declaration
            // order and exclude only those derived identifiers permanently.
            skip_multi_alias_ids: true,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum CompareVerdict {
    Equal,
    Differs(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CompareReport {
    verdict: CompareVerdict,
    multi_alias_axioms: usize,
}

fn compare_definitions(reference: Definition, actual: Definition) {
    let report = compare_definitions_with(reference, actual, CompareOptions::default());
    println!("multi-alias freezer axioms: {}", report.multi_alias_axioms);
    if let CompareVerdict::Differs(message) = report.verdict {
        panic!("{message}");
    }
}

fn compare_definitions_with(
    mut reference: Definition,
    mut actual: Definition,
    options: CompareOptions,
) -> CompareReport {
    let raw_reference = reference.clone();
    let raw_actual = actual.clone();
    strip_source_metadata(&mut reference);
    strip_source_metadata(&mut actual);
    let multi_alias_axioms = if options.skip_multi_alias_ids {
        let reference_count = strip_multi_alias_freezer_ids(&mut reference);
        let actual_count = strip_multi_alias_freezer_ids(&mut actual);
        reference_count.max(actual_count)
    } else {
        0
    };
    let verdict = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        compare_stripped_definitions(reference, actual, &raw_reference, &raw_actual)
    })) {
        Ok(()) => CompareVerdict::Equal,
        Err(panic) => CompareVerdict::Differs(panic_message(panic)),
    };
    CompareReport {
        verdict,
        multi_alias_axioms,
    }
}

fn compare_stripped_definitions(
    reference: Definition,
    actual: Definition,
    raw_reference: &Definition,
    raw_actual: &Definition,
) {
    assert_eq!(
        reference.attributes, actual.attributes,
        "definition attributes"
    );
    assert_eq!(
        reference.modules.len(),
        actual.modules.len(),
        "module count"
    );
    for (module_index, (reference, actual)) in
        reference.modules.iter().zip(&actual.modules).enumerate()
    {
        assert_eq!(reference.name, actual.name, "module name");
        assert_eq!(
            reference.attributes, actual.attributes,
            "{} attributes",
            reference.name
        );
        let reference_sentences = reference
            .sentences
            .iter()
            .map(canonical_sentence)
            .collect::<Vec<_>>();
        let actual_sentences = actual
            .sentences
            .iter()
            .map(canonical_sentence)
            .collect::<Vec<_>>();
        let reference_sentences = multiset(reference_sentences);
        let actual_sentences = multiset(actual_sentences);
        if reference_sentences != actual_sentences {
            let missing = count_differences(&reference_sentences, &actual_sentences);
            let extra = count_differences(&actual_sentences, &reference_sentences);
            let missing_ids = difference_ids(
                &missing,
                &reference.sentences,
                &raw_reference.modules[module_index].sentences,
            );
            let extra_ids = difference_ids(
                &extra,
                &actual.sentences,
                &raw_actual.modules[module_index].sentences,
            );
            panic!(
                "{} sentence multiset differs: reference={}, actual={} ({}); missing={} {:?}, extra={} {:?}\n{}\n{}\nmissing summaries:\n{}\nextra summaries:\n{}",
                reference.name,
                sentence_counts(&reference.sentences),
                sentence_counts(&actual.sentences),
                first_sentence_difference(&reference.sentences, &actual.sentences),
                missing.len(),
                missing_ids,
                extra.len(),
                extra_ids,
                difference_context(
                    missing.first().map(String::as_str),
                    extra.first().map(String::as_str)
                ),
                paired_difference_context(
                    &missing,
                    &extra,
                    &reference.sentences,
                    &actual.sentences,
                    &raw_reference.modules[module_index].sentences,
                    &raw_actual.modules[module_index].sentences,
                ),
                difference_summaries(
                    &missing,
                    &reference.sentences,
                    &raw_reference.modules[module_index].sentences,
                ),
                difference_summaries(
                    &extra,
                    &actual.sentences,
                    &raw_actual.modules[module_index].sentences,
                ),
            );
        }
    }
}

fn difference_summaries(differences: &[String], stripped: &[Sentence], raw: &[Sentence]) -> String {
    differences
        .iter()
        .enumerate()
        .filter_map(|(difference_index, difference)| {
            let sentence_index = stripped
                .iter()
                .position(|sentence| canonical_sentence(sentence) == *difference)?;
            let identity =
                sentence_identity(&raw[sentence_index]).unwrap_or_else(|| "<generated>".into());
            let kind = match &stripped[sentence_index] {
                Sentence::Import { .. } => "import",
                Sentence::SortDeclaration { .. } => "sort",
                Sentence::SymbolDeclaration { .. } => "symbol",
                Sentence::AliasDeclaration { .. } => "alias",
                Sentence::Axiom { .. } => "axiom",
                Sentence::Claim { .. } => "claim",
            };
            let excerpt = difference.chars().take(900).collect::<String>();
            Some(format!(
                "{}. {kind} {identity} (sentence {sentence_index}): {excerpt}",
                difference_index + 1
            ))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn paired_difference_context(
    missing: &[String],
    extra: &[String],
    stripped_reference: &[Sentence],
    stripped_actual: &[Sentence],
    raw_reference: &[Sentence],
    raw_actual: &[Sentence],
) -> String {
    for missing_sentence in missing {
        let Some(reference_index) = stripped_reference
            .iter()
            .position(|sentence| canonical_sentence(sentence) == *missing_sentence)
        else {
            continue;
        };
        let Some(identity) = sentence_identity(&raw_reference[reference_index]) else {
            continue;
        };
        if identity == "<generated>" {
            continue;
        }
        let actual_index = raw_actual
            .iter()
            .position(|sentence| sentence_identity(sentence).as_deref() == Some(&identity))
            .or_else(|| {
                let label = sentence_attribute(&raw_reference[reference_index], "label")?;
                raw_actual.iter().position(|sentence| {
                    sentence_attribute(sentence, "label").as_deref() == Some(&label)
                })
            });
        let Some(actual_index) = actual_index else {
            continue;
        };
        let actual_sentence = canonical_sentence(&stripped_actual[actual_index]);
        if extra.contains(&actual_sentence) {
            let reference_value = canonicalized_sentence(&stripped_reference[reference_index]);
            let actual_value = canonicalized_sentence(&stripped_actual[actual_index]);
            let competitor_context = match (
                owise_competitors(&reference_value),
                owise_competitors(&actual_value),
            ) {
                (Some(reference), Some(actual)) => {
                    let reference = multiset(
                        reference
                            .iter()
                            .map(|pattern| format!("{pattern:?}"))
                            .collect(),
                    );
                    let actual = multiset(
                        actual
                            .iter()
                            .map(|pattern| format!("{pattern:?}"))
                            .collect(),
                    );
                    let missing = count_differences(&reference, &actual);
                    let extra = count_differences(&actual, &reference);
                    format!(
                        "\ncompetitors: reference={}, actual={}, missing={}, extra={}\n{}",
                        reference.values().sum::<usize>(),
                        actual.values().sum::<usize>(),
                        missing.len(),
                        extra.len(),
                        difference_context(
                            missing.first().map(String::as_str),
                            extra.first().map(String::as_str),
                        )
                    )
                }
                _ => String::new(),
            };
            return format!(
                "paired difference for {identity}:\n{}{}",
                difference_context(Some(missing_sentence), Some(&actual_sentence)),
                competitor_context,
            );
        }
    }
    "no source-identified missing/extra pair".into()
}

fn sentence_attribute(sentence: &Sentence, name: &str) -> Option<String> {
    let attributes = match sentence {
        Sentence::Import { attributes, .. }
        | Sentence::SortDeclaration { attributes, .. }
        | Sentence::SymbolDeclaration { attributes, .. }
        | Sentence::AliasDeclaration { attributes, .. }
        | Sentence::Axiom { attributes, .. }
        | Sentence::Claim { attributes, .. } => attributes,
    };
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == name => {
            arguments.first().and_then(|argument| match argument {
                Pattern::String(value) => Some(value.clone()),
                _ => None,
            })
        }
        _ => None,
    })
}

fn owise_competitors(sentence: &Sentence) -> Option<&[Pattern]> {
    let Sentence::Axiom { pattern, .. } = sentence else {
        return None;
    };
    let Pattern::Implies { left, .. } = pattern.as_ref() else {
        return None;
    };
    let Pattern::And { arguments, .. } = left.as_ref() else {
        return None;
    };
    arguments.iter().find_map(|argument| {
        let Pattern::Not { argument, .. } = argument else {
            return None;
        };
        let Pattern::Or { arguments, .. } = argument.as_ref() else {
            return None;
        };
        Some(arguments.as_slice())
    })
}

fn difference_ids(differences: &[String], stripped: &[Sentence], raw: &[Sentence]) -> Vec<String> {
    differences
        .iter()
        .map(|difference| {
            stripped
                .iter()
                .position(|sentence| canonical_sentence(sentence) == *difference)
                .and_then(|index| sentence_identity(&raw[index]))
                .unwrap_or_else(|| "<generated>".into())
        })
        .collect()
}

fn sentence_identity(sentence: &Sentence) -> Option<String> {
    let attributes = match sentence {
        Sentence::Import { attributes, .. }
        | Sentence::SortDeclaration { attributes, .. }
        | Sentence::SymbolDeclaration { attributes, .. }
        | Sentence::AliasDeclaration { attributes, .. }
        | Sentence::Axiom { attributes, .. }
        | Sentence::Claim { attributes, .. } => attributes,
    };
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments }
            if symbol.name == "UNIQUE'Unds'ID"
                || symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Source" =>
        {
            arguments.first().and_then(|argument| match argument {
                Pattern::String(value) => Some(value.clone()),
                _ => None,
            })
        }
        _ => None,
    })
}

fn canonical_sentence(sentence: &Sentence) -> String {
    format!("{:?}", canonicalized_sentence(sentence))
}

fn canonicalized_sentence(sentence: &Sentence) -> Sentence {
    let mut sentence = sentence.clone();
    match &mut sentence {
        Sentence::AliasDeclaration {
            left,
            right,
            attributes,
            ..
        } => {
            canonicalize_pattern(left);
            canonicalize_pattern(right);
            canonicalize_attributes(attributes);
        }
        Sentence::Axiom {
            pattern,
            attributes,
            ..
        }
        | Sentence::Claim {
            pattern,
            attributes,
            ..
        } => {
            canonicalize_pattern(pattern);
            canonicalize_attributes(attributes);
        }
        Sentence::Import { attributes, .. }
        | Sentence::SortDeclaration { attributes, .. }
        | Sentence::SymbolDeclaration { attributes, .. } => {
            canonicalize_attributes(attributes);
        }
    }
    sentence
}

fn canonicalize_attributes(attributes: &mut Attributes) {
    for attribute in &mut attributes.0 {
        canonicalize_pattern(attribute);
    }
}

fn canonicalize_pattern(pattern: &mut Pattern) {
    rename_generated_variables(pattern);
    canonicalize_existentials(pattern);
    alpha_normalize_bound_variables(pattern);
    // Bound names participate in `Pattern::Ord`, so re-sort disjunctions after replacing them.
    canonicalize_existentials(pattern);
}

fn alpha_normalize_bound_variables(pattern: &mut Pattern) {
    fn visit(pattern: &mut Pattern, scopes: &mut Vec<(k_rust::kore::ast::Variable, String)>) {
        match pattern {
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    visit(argument, scopes);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => visit(argument, scopes),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                visit(left, scopes);
                visit(right, scopes);
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                let original = variable.clone();
                let canonical = format!("#KDiffBound{}", scopes.len());
                variable.name.clone_from(&canonical);
                scopes.push((original, canonical));
                visit(body, scopes);
                scopes.pop();
            }
            Pattern::Variable(variable) => {
                if let Some((_, canonical)) = scopes.iter().rev().find(|(bound, _)| {
                    bound.kind == variable.kind
                        && bound.name == variable.name
                        && bound.sort == variable.sort
                }) {
                    variable.name.clone_from(canonical);
                }
            }
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }

    visit(pattern, &mut Vec::new());
}

fn canonicalize_existentials(pattern: &mut Pattern) {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                canonicalize_existentials(argument);
            }
        }
        Pattern::Or { sort, arguments } => {
            for argument in arguments.iter_mut() {
                canonicalize_existentials(argument);
            }
            let mut flattened = Vec::new();
            for mut argument in std::mem::take(arguments) {
                let nested = match &mut argument {
                    Pattern::Or {
                        sort: nested_sort,
                        arguments: nested,
                    } if *nested_sort == *sort => Some(std::mem::take(nested)),
                    _ => None,
                };
                if let Some(mut nested) = nested {
                    flattened.append(&mut nested);
                } else {
                    flattened.push(argument);
                }
            }
            flattened.sort();
            *arguments = flattened;
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => canonicalize_existentials(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            canonicalize_existentials(left);
            canonicalize_existentials(right);
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => {
            canonicalize_existentials(body);
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
        Pattern::Variable(_) => {}
    }

    #[derive(Clone, Copy)]
    enum Quantifier {
        Exists,
        Forall,
    }
    let quantifier = match pattern {
        Pattern::Exists { .. } => Quantifier::Exists,
        Pattern::Forall { .. } => Quantifier::Forall,
        _ => return,
    };
    let mut current = std::mem::replace(pattern, Pattern::String(String::new()));
    let mut binders = Vec::new();
    loop {
        let fields = match (quantifier, &mut current) {
            (
                Quantifier::Exists,
                Pattern::Exists {
                    sort,
                    variable,
                    body,
                },
            )
            | (
                Quantifier::Forall,
                Pattern::Forall {
                    sort,
                    variable,
                    body,
                },
            ) => Some((
                sort.clone(),
                variable.clone(),
                std::mem::replace(body.as_mut(), Pattern::String(String::new())),
            )),
            _ => None,
        };
        let Some((sort, variable, body)) = fields else {
            break;
        };
        binders.push((sort, variable));
        current = body;
    }
    binders.sort_by(|left, right| {
        let key = |(_, variable): &(_, k_rust::kore::ast::Variable)| {
            (variable.name.clone(), variable.sort.clone(), variable.kind)
        };
        key(left).cmp(&key(right))
    });
    for (sort, variable) in binders.into_iter().rev() {
        current = match quantifier {
            Quantifier::Exists => Pattern::Exists {
                sort,
                variable,
                body: Box::new(current),
            },
            Quantifier::Forall => Pattern::Forall {
                sort,
                variable,
                body: Box::new(current),
            },
        };
    }
    *pattern = current;
}

fn generated_stem(name: &str) -> Option<&str> {
    if let Some(suffix) = name.strip_prefix("Var'Unds'") {
        if suffix.contains("'Hash'KDiff") {
            return None;
        }
        let stem = suffix.trim_end_matches(|character: char| character.is_ascii_digit());
        if !stem.is_empty() && stem.len() != suffix.len() {
            return Some(stem);
        }
    }
    None
}

fn rename_generated_variables(pattern: &mut Pattern) {
    fn visit(pattern: &mut Pattern, indices: &mut BTreeMap<String, usize>) {
        let mut rename = |variable: &mut k_rust::kore::ast::Variable| {
            let Some(stem) = generated_stem(&variable.name) else {
                return;
            };
            let stem = stem.to_owned();
            let next = indices.len();
            let index = *indices.entry(variable.name.clone()).or_insert(next);
            // KORE identifiers encode punctuation in apostrophe-delimited
            // words. A raw `#` would make N15's serialized implication inputs
            // unparsable by both kore-parser and krust.
            variable.name = format!("Var'Unds'{stem}'Hash'KDiff{index}");
        };

        match pattern {
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    visit(argument, indices);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => visit(argument, indices),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                visit(left, indices);
                visit(right, indices);
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                rename(variable);
                visit(body, indices);
            }
            Pattern::Variable(variable) => rename(variable),
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }

    visit(pattern, &mut BTreeMap::new());
}

fn strip_source_metadata(definition: &mut Definition) {
    strip_attributes(&mut definition.attributes);
    for module in &mut definition.modules {
        strip_attributes(&mut module.attributes);
        for sentence in &mut module.sentences {
            let attributes = match sentence {
                Sentence::Import { attributes, .. }
                | Sentence::SortDeclaration { attributes, .. }
                | Sentence::SymbolDeclaration { attributes, .. }
                | Sentence::AliasDeclaration { attributes, .. }
                | Sentence::Axiom { attributes, .. }
                | Sentence::Claim { attributes, .. } => attributes,
            };
            strip_attributes(attributes);
        }
    }
}

fn strip_multi_alias_freezer_ids(definition: &mut Definition) -> usize {
    let mut stripped = 0;
    for module in &mut definition.modules {
        let freezers = multi_alias_freezer(module);
        if freezers.is_empty() {
            continue;
        }
        for sentence in &mut module.sentences {
            let Sentence::Axiom {
                pattern,
                attributes,
                ..
            } = sentence
            else {
                continue;
            };
            if pattern_mentions_any_symbol(pattern, &freezers) {
                strip_unique_id_attributes(attributes);
                stripped += 1;
            }
        }
    }
    stripped
}

fn multi_alias_freezer(module: &k_rust::kore::ast::Module) -> BTreeSet<String> {
    let mut by_hint = BTreeMap::<String, Vec<String>>::new();
    for sentence in &module.sentences {
        let Sentence::SymbolDeclaration { symbol, .. } = sentence else {
            continue;
        };
        let Some(hint) = multi_alias_freezer_hint(&symbol.name) else {
            continue;
        };
        by_hint
            .entry(hint.into())
            .or_default()
            .push(symbol.name.clone());
    }
    by_hint
        .into_values()
        .filter(|names| names.len() > 1)
        .flatten()
        .collect()
}

fn multi_alias_freezer_hint(name: &str) -> Option<&str> {
    let suffix = name.strip_prefix("Lbl'Hash'freezer")?;
    let (hint, number) = suffix.rsplit_once("'Unds'")?;
    (!hint.is_empty() && !number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit()))
        .then_some(hint)
}

fn pattern_mentions_any_symbol(pattern: &Pattern, symbols: &BTreeSet<String>) -> bool {
    match pattern {
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            symbols.contains(&symbol.name)
                || arguments
                    .iter()
                    .any(|argument| pattern_mentions_any_symbol(argument, symbols))
        }
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => arguments
            .iter()
            .any(|argument| pattern_mentions_any_symbol(argument, symbols)),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => pattern_mentions_any_symbol(argument, symbols),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            pattern_mentions_any_symbol(left, symbols)
                || pattern_mentions_any_symbol(right, symbols)
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => pattern_mentions_any_symbol(body, symbols),
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => false,
    }
}

fn strip_unique_id_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. } if symbol.name == "UNIQUE'Unds'ID"
        )
    });
}

fn strip_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. }
                if symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Location"
                    || symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Source"
        )
    });
}

fn multiset(values: Vec<String>) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for value in values {
        *counts.entry(value).or_default() += 1;
    }
    counts
}

fn count_differences(
    left: &BTreeMap<String, usize>,
    right: &BTreeMap<String, usize>,
) -> Vec<String> {
    left.iter()
        .flat_map(|(sentence, left_count)| {
            let difference =
                left_count.saturating_sub(right.get(sentence).copied().unwrap_or_default());
            std::iter::repeat_n(sentence.clone(), difference)
        })
        .collect()
}

fn difference_context(reference: Option<&str>, actual: Option<&str>) -> String {
    let (Some(reference), Some(actual)) = (reference, actual) else {
        return format!(
            "missing: {}\nextra: {}",
            reference.unwrap_or("none"),
            actual.unwrap_or("none")
        );
    };
    let reference = reference.chars().collect::<Vec<_>>();
    let actual = actual.chars().collect::<Vec<_>>();
    let index = reference
        .iter()
        .zip(&actual)
        .position(|(reference, actual)| reference != actual)
        .unwrap_or_else(|| reference.len().min(actual.len()));
    let start = index.saturating_sub(250);
    let end = (index + 1800).min(reference.len().max(actual.len()));
    let excerpt = |value: &[char]| {
        value[start.min(value.len())..end.min(value.len())]
            .iter()
            .collect::<String>()
    };
    format!(
        "first difference at character {index}\nreference: …{}…\nactual:    …{}…",
        excerpt(&reference),
        excerpt(&actual)
    )
}

fn sentence_counts(sentences: &[Sentence]) -> String {
    let mut counts = [0; 6];
    for sentence in sentences {
        counts[match sentence {
            Sentence::Import { .. } => 0,
            Sentence::SortDeclaration { .. } => 1,
            Sentence::SymbolDeclaration { .. } => 2,
            Sentence::AliasDeclaration { .. } => 3,
            Sentence::Axiom { .. } => 4,
            Sentence::Claim { .. } => 5,
        }] += 1;
    }
    format!(
        "imports={}, sorts={}, symbols={}, aliases={}, axioms={}, claims={}",
        counts[0], counts[1], counts[2], counts[3], counts[4], counts[5]
    )
}

fn first_sentence_difference(reference: &[Sentence], actual: &[Sentence]) -> String {
    reference
        .iter()
        .zip(actual)
        .position(|(reference, actual)| reference != actual)
        .map_or_else(
            || "common prefix is identical".into(),
            |index| format!("first differing sentence={index}"),
        )
}
