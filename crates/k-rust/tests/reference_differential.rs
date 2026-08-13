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
                "{} sentence multiset differs: reference={}, actual={} ({}); missing={} {:?}, extra={} {:?}\n{}",
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
            );
        }
    }
}

fn difference_ids(differences: &[String], stripped: &[Sentence], raw: &[Sentence]) -> Vec<String> {
    differences
        .iter()
        .take(8)
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
    let mut source = format!("{sentence:?}");
    for prefix in ["Var'Unds'Gen", "Var'Unds'DotVar"] {
        let mut canonical = String::with_capacity(source.len());
        let mut remaining = source.as_str();
        while let Some(index) = remaining.find(prefix) {
            canonical.push_str(&remaining[..index]);
            canonical.push_str(prefix);
            remaining = &remaining[index + prefix.len()..];
            remaining = remaining.trim_start_matches(|character: char| character.is_ascii_digit());
        }
        canonical.push_str(remaining);
        source = canonical;
    }
    source
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
