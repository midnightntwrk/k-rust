use std::{collections::BTreeMap, env, fs};

use k_rust::kore::{
    ast::{Attributes, Definition, Pattern, Sentence},
    parser::parse_definition,
};

#[test]
#[ignore = "requires K_REFERENCE_KORE and K_RUST_KORE outputs"]
fn emitted_kore_matches_the_reference_frontend() {
    let reference_path = env::var("K_REFERENCE_KORE").expect("K_REFERENCE_KORE is required");
    let actual_path = env::var("K_RUST_KORE").expect("K_RUST_KORE is required");
    let reference_source = fs::read_to_string(&reference_path).unwrap();
    let actual_source = fs::read_to_string(&actual_path).unwrap();
    let mut reference = parse_definition(&reference_source).unwrap();
    let mut actual = parse_definition(&actual_source).unwrap();
    let raw_reference = reference.clone();
    let raw_actual = actual.clone();
    strip_source_metadata(&mut reference);
    strip_source_metadata(&mut actual);

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
            canonicalize_existentials(left);
            canonicalize_existentials(right);
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
            canonicalize_existentials(pattern);
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
        canonicalize_existentials(attribute);
    }
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
            for argument in std::mem::take(arguments) {
                match argument {
                    Pattern::Or {
                        sort: nested_sort,
                        arguments: nested,
                    } if nested_sort == *sort => flattened.extend(nested),
                    argument => flattened.push(argument),
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
        Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. }
        | Pattern::Mu { variable, body }
        | Pattern::Nu { variable, body } => {
            variable.name = canonical_generated_name(&variable.name);
            canonicalize_existentials(body);
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
        Pattern::Variable(variable) => {
            variable.name = canonical_generated_name(&variable.name);
        }
    }

    if !matches!(pattern, Pattern::Exists { .. }) {
        return;
    }
    let mut current = std::mem::replace(pattern, Pattern::String(String::new()));
    let mut binders = Vec::new();
    while let Pattern::Exists {
        sort,
        variable,
        body,
    } = current
    {
        binders.push((sort, variable));
        current = *body;
    }
    binders.sort_by(|left, right| {
        let key = |(_, variable): &(_, k_rust::kore::ast::Variable)| {
            (
                canonical_generated_name(&variable.name),
                variable.sort.clone(),
                variable.kind,
            )
        };
        key(left).cmp(&key(right))
    });
    for (sort, variable) in binders.into_iter().rev() {
        current = Pattern::Exists {
            sort,
            variable,
            body: Box::new(current),
        };
    }
    *pattern = current;
}

fn canonical_generated_name(name: &str) -> String {
    for prefix in ["Var'Unds'Gen", "Var'Unds'DotVar"] {
        if let Some(suffix) = name.strip_prefix(prefix)
            && suffix.chars().all(|character| character.is_ascii_digit())
        {
            return prefix.into();
        }
    }
    if let Some(suffix) = name.strip_prefix("Var'Unds'") {
        let stem = suffix.trim_end_matches(|character: char| character.is_ascii_digit());
        if !stem.is_empty() && stem.len() != suffix.len() {
            return format!("Var'Unds'{stem}");
        }
    }
    name.into()
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

fn strip_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. }
                if symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Location"
                    || symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Source"
                    || symbol.name == "UNIQUE'Unds'ID"
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
