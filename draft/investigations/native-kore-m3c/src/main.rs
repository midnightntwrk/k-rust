use std::{collections::BTreeMap, env, error::Error, fs};

use k_rust::kore::{
    ast::{Attributes, Module, Pattern, Sentence, Sort, Variable, VariableKind},
    parser::parse_definition,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("native-kore-m3c-delta: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    let reference = fs::read_to_string(arguments.next().ok_or("missing reference KORE")?)?;
    let actual = fs::read_to_string(arguments.next().ok_or("missing native KORE")?)?;
    let module_name = arguments
        .next()
        .ok_or("missing module name")?
        .into_string()
        .map_err(|_| "module name is not UTF-8")?;
    if arguments.next().is_some() {
        return Err("expected REFERENCE ACTUAL MODULE".into());
    }

    let reference = parse_definition(&reference)?;
    let actual = parse_definition(&actual)?;
    let reference = normalized_module(&reference.modules, &module_name)?;
    let actual = normalized_module(&actual.modules, &module_name)?;
    emit_stage("metadata-only", &reference, &actual);

    let mut reference_alpha = reference.clone();
    let mut actual_alpha = actual.clone();
    alpha_normalize_module(&mut reference_alpha);
    alpha_normalize_module(&mut actual_alpha);
    emit_stage("alpha", &reference_alpha, &actual_alpha);

    normalize_rule_labels(&mut reference_alpha, &module_name);
    normalize_rule_labels(&mut actual_alpha, &module_name);
    emit_stage("alpha+labels", &reference_alpha, &actual_alpha);

    let mut reference_without_projections = reference_alpha.clone();
    let mut actual_without_projections = actual_alpha.clone();
    reference_without_projections
        .sentences
        .retain(|sentence| !has_named_projection(sentence));
    actual_without_projections
        .sentences
        .retain(|sentence| !has_named_projection(sentence));
    emit_stage(
        "alpha+labels+named-projection-policy",
        &reference_without_projections,
        &actual_without_projections,
    );

    remove_attribute(&mut reference_alpha, "cool-like");
    remove_attribute(&mut actual_alpha, "cool-like");
    emit_stage("alpha+labels+cool-like-policy", &reference_alpha, &actual_alpha);

    reference_alpha
        .sentences
        .retain(|sentence| !has_named_projection(sentence));
    actual_alpha
        .sentences
        .retain(|sentence| !has_named_projection(sentence));
    emit_stage(
        "alpha+labels+cool-like-policy+named-projection-policy",
        &reference_alpha,
        &actual_alpha,
    );

    let reference = sentence_multiset(&reference.sentences);
    let actual = sentence_multiset(&actual.sentences);

    println!(
        "COUNTS\treference={}\tactual={}",
        reference.values().sum::<usize>(),
        actual.values().sum::<usize>()
    );
    emit_difference("MISSING", &reference, &actual);
    emit_difference("EXTRA", &actual, &reference);
    Ok(())
}

fn emit_stage(name: &str, reference: &Module, actual: &Module) {
    let reference = sentence_multiset(&reference.sentences);
    let actual = sentence_multiset(&actual.sentences);
    let missing = difference_count(&reference, &actual);
    let extra = difference_count(&actual, &reference);
    println!(
        "STAGE\t{name}\treference={}\tactual={}\tmissing={missing}\textra={extra}",
        reference.values().sum::<usize>(),
        actual.values().sum::<usize>(),
    );
}

fn difference_count(left: &BTreeMap<String, usize>, right: &BTreeMap<String, usize>) -> usize {
    left.iter()
        .map(|(sentence, count)| count.saturating_sub(right.get(sentence).copied().unwrap_or(0)))
        .sum()
}

fn alpha_normalize_module(module: &mut Module) {
    for sentence in &mut module.sentences {
        let mut names = BTreeMap::<(VariableKind, String, Sort), String>::new();
        for pattern in sentence_patterns_mut(sentence) {
            alpha_normalize_pattern(pattern, &mut names);
        }
    }
}

fn sentence_patterns_mut(sentence: &mut Sentence) -> Vec<&mut Pattern> {
    match sentence {
        Sentence::Import { attributes, .. }
        | Sentence::SortDeclaration { attributes, .. }
        | Sentence::SymbolDeclaration { attributes, .. } => attributes.0.iter_mut().collect(),
        Sentence::AliasDeclaration {
            left,
            right,
            attributes,
            ..
        } => {
            let mut patterns = vec![left.as_mut(), right.as_mut()];
            patterns.extend(attributes.0.iter_mut());
            patterns
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
            let mut patterns = vec![pattern.as_mut()];
            patterns.extend(attributes.0.iter_mut());
            patterns
        }
    }
}

fn alpha_normalize_pattern(
    pattern: &mut Pattern,
    names: &mut BTreeMap<(VariableKind, String, Sort), String>,
) {
    match pattern {
        Pattern::Variable(variable) => alpha_normalize_variable(variable, names),
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                alpha_normalize_pattern(argument, names);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => alpha_normalize_pattern(argument, names),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            alpha_normalize_pattern(left, names);
            alpha_normalize_pattern(right, names);
        }
        Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. }
        | Pattern::Mu { variable, body }
        | Pattern::Nu { variable, body } => {
            alpha_normalize_variable(variable, names);
            alpha_normalize_pattern(body, names);
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

fn alpha_normalize_variable(
    variable: &mut Variable,
    names: &mut BTreeMap<(VariableKind, String, Sort), String>,
) {
    let key = (variable.kind, variable.name.clone(), variable.sort.clone());
    let next = names.len();
    variable.name = names
        .entry(key)
        .or_insert_with(|| format!("VarAlpha{next}"))
        .clone();
}

fn normalize_rule_labels(module: &mut Module, module_name: &str) {
    let prefix = format!("{module_name}.");
    for sentence in &mut module.sentences {
        let attributes = sentence_attributes_mut(sentence);
        for attribute in &mut attributes.0 {
            let Pattern::Application { symbol, arguments } = attribute else {
                continue;
            };
            if symbol.name != "label" {
                continue;
            }
            if let [Pattern::String(label)] = arguments.as_mut_slice()
                && let Some(unqualified) = label.strip_prefix(&prefix)
            {
                *label = unqualified.to_owned();
            }
        }
        attributes.0.sort();
    }
}

fn remove_attribute(module: &mut Module, name: &str) {
    for sentence in &mut module.sentences {
        let attributes = sentence_attributes_mut(sentence);
        attributes.0.retain(|attribute| {
            !matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == name)
        });
        attributes.0.sort();
    }
}

fn sentence_attributes_mut(sentence: &mut Sentence) -> &mut Attributes {
    match sentence {
        Sentence::Import { attributes, .. }
        | Sentence::SortDeclaration { attributes, .. }
        | Sentence::SymbolDeclaration { attributes, .. }
        | Sentence::AliasDeclaration { attributes, .. }
        | Sentence::Axiom { attributes, .. }
        | Sentence::Claim { attributes, .. } => attributes,
    }
}

fn has_named_projection(sentence: &Sentence) -> bool {
    match sentence {
        Sentence::SymbolDeclaration { symbol, .. } => is_named_projection(&symbol.name),
        Sentence::Axiom { pattern, .. } | Sentence::Claim { pattern, .. } => {
            pattern_has_named_projection(pattern)
        }
        Sentence::AliasDeclaration { left, right, .. } => {
            pattern_has_named_projection(left) || pattern_has_named_projection(right)
        }
        Sentence::Import { .. } | Sentence::SortDeclaration { .. } => false,
    }
}

fn is_named_projection(name: &str) -> bool {
    name.starts_with("Lblproject'Coln'") && name.matches("'Coln'").count() >= 2
}

fn pattern_has_named_projection(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication { symbol, arguments, .. } => {
            is_named_projection(&symbol.name)
                || arguments.iter().any(pattern_has_named_projection)
        }
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            arguments.iter().any(pattern_has_named_projection)
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. }
        | Pattern::Exists { body: argument, .. }
        | Pattern::Forall { body: argument, .. }
        | Pattern::Mu { body: argument, .. }
        | Pattern::Nu { body: argument, .. } => pattern_has_named_projection(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            pattern_has_named_projection(left) || pattern_has_named_projection(right)
        }
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => false,
    }
}

fn normalized_module(modules: &[Module], name: &str) -> Result<Module, Box<dyn Error>> {
    let mut matches = modules.iter().filter(|module| module.name == name);
    let mut module = matches
        .next()
        .ok_or_else(|| format!("KORE module {name:?} is absent"))?
        .clone();
    if matches.next().is_some() {
        return Err(format!("KORE module {name:?} occurs more than once").into());
    }
    normalize_attributes(&mut module.attributes);
    for sentence in &mut module.sentences {
        let attributes = match sentence {
            Sentence::Import { attributes, .. }
            | Sentence::SortDeclaration { attributes, .. }
            | Sentence::SymbolDeclaration { attributes, .. }
            | Sentence::AliasDeclaration { attributes, .. }
            | Sentence::Axiom { attributes, .. }
            | Sentence::Claim { attributes, .. } => attributes,
        };
        normalize_attributes(attributes);
    }
    Ok(module)
}

fn normalize_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. }
                if symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Location"
                    || symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Source"
                    || symbol.name == "UNIQUE'Unds'ID"
                    || symbol.name == "contentStartLine"
                    || symbol.name == "digest"
        )
    });
    attributes.0.sort();
}

fn sentence_multiset(sentences: &[Sentence]) -> BTreeMap<String, usize> {
    let mut result = BTreeMap::new();
    for sentence in sentences {
        *result.entry(canonical_sentence(sentence)).or_default() += 1;
    }
    result
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

fn emit_difference(
    side: &str,
    left: &BTreeMap<String, usize>,
    right: &BTreeMap<String, usize>,
) {
    let mut ordinal = 0;
    for (sentence, left_count) in left {
        let count = left_count.saturating_sub(right.get(sentence).copied().unwrap_or_default());
        for _ in 0..count {
            ordinal += 1;
            println!("{side}\t{ordinal:03}\t{sentence}");
        }
    }
}
