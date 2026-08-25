//! Fail-closed native/reference KORE comparison for the M4 complete-IMP gate.
//!
//! The only structural allowance beyond metadata and per-sentence alpha
//! normalization is a mechanically proven, complete, closed, unused pair made
//! from one structured-adapter named projector declaration and its one defining
//! equation. A projector-looking prefix is never sufficient for exclusion.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use k_rust::kore::ast::{
    Attributes, Module, Pattern, Sentence, Sort, Variable, VariableKind,
};
use k_rust::kore::parser::parse_definition;

const PROJECTOR_PREFIX: &str = "Lblproject'Coln'";
const PROJECTOR_SEPARATOR: &str = "'Coln'";

/// An explicitly reviewed label rewrite. Empty by default: label spelling is
/// semantic and current KRS/reference output is expected to agree literally.
#[derive(Clone, Debug, Default)]
pub struct ComparePolicy {
    pub label_map: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComparisonReport {
    pub reference_sentences: usize,
    pub actual_sentences: usize,
    pub reference_projector_pairs: usize,
    pub actual_projector_pairs: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompareError(String);

impl CompareError {
    fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for CompareError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

impl std::error::Error for CompareError {}

/// Parse, validate, normalize, and compare one explicitly named module.
pub fn compare_kore(
    reference_source: &str,
    actual_source: &str,
    module_name: &str,
    policy: &ComparePolicy,
) -> Result<ComparisonReport, CompareError> {
    if module_name.is_empty() {
        return Err(CompareError::new("module name must not be empty"));
    }
    let reference = parse_definition(reference_source)
        .map_err(|error| CompareError::new(format!("cannot parse reference KORE: {error}")))?;
    let actual = parse_definition(actual_source)
        .map_err(|error| CompareError::new(format!("cannot parse native KORE: {error}")))?;
    let mut reference = select_module(&reference.modules, module_name, "reference")?;
    let mut actual = select_module(&actual.modules, module_name, "native")?;

    normalize_module(&mut reference, policy)?;
    normalize_module(&mut actual, policy)?;
    validate_claims(&reference, "reference")?;
    validate_claims(&actual, "native")?;

    let reference_projector_pairs = remove_closed_projector_pairs(&mut reference, "reference")?;
    let actual_projector_pairs = remove_closed_projector_pairs(&mut actual, "native")?;
    let reference_sentences = reference.sentences.len();
    let actual_sentences = actual.sentences.len();

    let reference_multiset = sentence_multiset(&reference.sentences);
    let actual_multiset = sentence_multiset(&actual.sentences);
    let missing = difference(&reference_multiset, &actual_multiset);
    let extra = difference(&actual_multiset, &reference_multiset);
    if !missing.is_empty() || !extra.is_empty() {
        return Err(CompareError::new(format_difference(
            reference_sentences,
            actual_sentences,
            &missing,
            &extra,
        )));
    }

    Ok(ComparisonReport {
        reference_sentences,
        actual_sentences,
        reference_projector_pairs,
        actual_projector_pairs,
    })
}

fn select_module(
    modules: &[Module],
    name: &str,
    route: &str,
) -> Result<Module, CompareError> {
    let matches = modules
        .iter()
        .filter(|module| module.name == name)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [module] => Ok((*module).clone()),
        [] => Err(CompareError::new(format!(
            "{route} KORE module {name:?} is absent"
        ))),
        _ => Err(CompareError::new(format!(
            "{route} KORE module {name:?} occurs more than once"
        ))),
    }
}

fn normalize_module(module: &mut Module, policy: &ComparePolicy) -> Result<(), CompareError> {
    normalize_attributes(&mut module.attributes);
    for sentence in &mut module.sentences {
        normalize_attributes(sentence_attributes_mut(sentence));
        normalize_labels(sentence_attributes_mut(sentence), policy)?;
        alpha_normalize_sentence(sentence);
    }
    Ok(())
}

fn normalize_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. }
                if matches!(
                    symbol.name.as_str(),
                    "org'Stop'kframework'Stop'attributes'Stop'Location"
                        | "org'Stop'kframework'Stop'attributes'Stop'Source"
                        | "UNIQUE'Unds'ID"
                        | "contentStartLine"
                        | "digest"
                )
        )
    });
    attributes.0.sort();
}

fn normalize_labels(
    attributes: &mut Attributes,
    policy: &ComparePolicy,
) -> Result<(), CompareError> {
    for attribute in &mut attributes.0 {
        let Pattern::Application { symbol, arguments } = attribute else {
            continue;
        };
        if symbol.name != "label" {
            continue;
        }
        let [Pattern::String(label)] = arguments.as_mut_slice() else {
            return Err(CompareError::new("label attribute is not exactly one string"));
        };
        if let Some(mapped) = policy.label_map.get(label) {
            *label = mapped.clone();
        }
    }
    attributes.0.sort();
    Ok(())
}

fn alpha_normalize_sentence(sentence: &mut Sentence) {
    let mut names = BTreeMap::<(VariableKind, String, Sort), String>::new();
    for pattern in sentence_patterns_mut(sentence) {
        alpha_normalize_pattern(pattern, &mut names);
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

fn remove_closed_projector_pairs(
    module: &mut Module,
    route: &str,
) -> Result<usize, CompareError> {
    let mut candidate_names = BTreeSet::new();
    for sentence in &module.sentences {
        if let Sentence::SymbolDeclaration { symbol, .. } = sentence
            && named_projector_parts(&symbol.name).is_some()
        {
            candidate_names.insert(symbol.name.clone());
        }
        visit_sentence_symbols(sentence, &mut |name| {
            if named_projector_parts(name).is_some() {
                candidate_names.insert(name.to_owned());
            }
        });
    }

    let mut excluded = BTreeSet::new();
    for name in &candidate_names {
        let declarations = module
            .sentences
            .iter()
            .enumerate()
            .filter_map(|(index, sentence)| match sentence {
                Sentence::SymbolDeclaration {
                    hooked,
                    symbol,
                    argument_sorts,
                    attributes,
                    ..
                } if symbol.name == *name => Some((index, *hooked, argument_sorts, attributes)),
                _ => None,
            })
            .collect::<Vec<_>>();
        let [(declaration_index, false, argument_sorts, attributes)] = declarations.as_slice()
        else {
            return Err(CompareError::new(format!(
                "{route} named projector {name:?} does not have exactly one unhooked declaration"
            )));
        };
        if argument_sorts.len() != 1 || !has_nullary_attribute(attributes, "function") {
            return Err(CompareError::new(format!(
                "{route} named projector {name:?} declaration is not a unary function"
            )));
        }

        let definitions = module
            .sentences
            .iter()
            .enumerate()
            .filter_map(|(index, sentence)| {
                is_projector_definition(sentence, name).then_some(index)
            })
            .collect::<Vec<_>>();
        let [definition_index] = definitions.as_slice() else {
            return Err(CompareError::new(format!(
                "{route} named projector {name:?} does not have exactly one generated equation"
            )));
        };

        let mut occurrences = Vec::new();
        for (index, sentence) in module.sentences.iter().enumerate() {
            let mut count = 0;
            visit_sentence_symbols(sentence, &mut |seen| {
                if seen == name {
                    count += 1;
                }
            });
            if count != 0 {
                occurrences.push((index, count));
            }
        }
        if occurrences.as_slice() != [(*definition_index, 1)] {
            return Err(CompareError::new(format!(
                "{route} named projector {name:?} is not closed and unused; occurrences={occurrences:?}"
            )));
        }
        excluded.insert(*declaration_index);
        excluded.insert(*definition_index);
    }

    module.sentences = module
        .sentences
        .drain(..)
        .enumerate()
        .filter_map(|(index, sentence)| (!excluded.contains(&index)).then_some(sentence))
        .collect();
    Ok(candidate_names.len())
}

fn named_projector_parts(name: &str) -> Option<(&str, &str)> {
    let suffix = name.strip_prefix(PROJECTOR_PREFIX)?;
    let (owner, field) = suffix.split_once(PROJECTOR_SEPARATOR)?;
    if owner.is_empty() || field.is_empty() || field.contains(PROJECTOR_SEPARATOR) {
        return None;
    }
    Some((owner, field))
}

fn is_projector_definition(sentence: &Sentence, name: &str) -> bool {
    let Sentence::Axiom { pattern, .. } = sentence else {
        return false;
    };
    let Pattern::Implies { right, .. } = pattern.as_ref() else {
        return false;
    };
    let Pattern::Equals { left, .. } = right.as_ref() else {
        return false;
    };
    matches!(
        left.as_ref(),
        Pattern::Application { symbol, arguments }
            if symbol.name == name && arguments.len() == 1
    )
}

fn validate_claims(module: &Module, route: &str) -> Result<(), CompareError> {
    let mut labels = BTreeSet::new();
    for sentence in &module.sentences {
        let Sentence::Claim {
            pattern,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if !matches!(pattern.as_ref(), Pattern::Implies { .. }) {
            return Err(CompareError::new(format!(
                "{route} claim body is not an implication"
            )));
        }
        for forbidden in ["priority", "owise", "all-path"] {
            if has_attribute(attributes, forbidden) {
                return Err(CompareError::new(format!(
                    "{route} claim carries forbidden {forbidden:?} metadata"
                )));
            }
        }
        let label = string_attribute(attributes, "label")?.ok_or_else(|| {
            CompareError::new(format!("{route} claim has no exact string label"))
        })?;
        if !labels.insert(label.to_owned()) {
            return Err(CompareError::new(format!(
                "{route} claim label {label:?} occurs more than once"
            )));
        }
    }
    Ok(())
}

fn string_attribute<'a>(
    attributes: &'a Attributes,
    name: &str,
) -> Result<Option<&'a str>, CompareError> {
    let matches = attributes
        .0
        .iter()
        .filter_map(|attribute| match attribute {
            Pattern::Application { symbol, arguments } if symbol.name == name => Some(arguments),
            _ => None,
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [] => Ok(None),
        [arguments] => match arguments.as_slice() {
            [Pattern::String(value)] => Ok(Some(value)),
            _ => Err(CompareError::new(format!(
                "{name} attribute is not exactly one string"
            ))),
        },
        _ => Err(CompareError::new(format!(
            "{name} attribute occurs more than once"
        ))),
    }
}

fn has_attribute(attributes: &Attributes, name: &str) -> bool {
    attributes.0.iter().any(
        |attribute| matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == name),
    )
}

fn has_nullary_attribute(attributes: &Attributes, name: &str) -> bool {
    attributes.0.iter().any(|attribute| {
        matches!(
            attribute,
            Pattern::Application { symbol, arguments }
                if symbol.name == name && arguments.is_empty()
        )
    })
}

fn visit_sentence_symbols(sentence: &Sentence, visitor: &mut impl FnMut(&str)) {
    for pattern in sentence_patterns(sentence) {
        visit_pattern_symbols(pattern, visitor);
    }
}

fn visit_pattern_symbols(pattern: &Pattern, visitor: &mut impl FnMut(&str)) {
    match pattern {
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            visitor(&symbol.name);
            for argument in arguments {
                visit_pattern_symbols(argument, visitor);
            }
        }
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            for argument in arguments {
                visit_pattern_symbols(argument, visitor);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. }
        | Pattern::Exists { body: argument, .. }
        | Pattern::Forall { body: argument, .. }
        | Pattern::Mu { body: argument, .. }
        | Pattern::Nu { body: argument, .. } => visit_pattern_symbols(argument, visitor),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            visit_pattern_symbols(left, visitor);
            visit_pattern_symbols(right, visitor);
        }
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

fn sentence_patterns(sentence: &Sentence) -> Vec<&Pattern> {
    match sentence {
        Sentence::Import { attributes, .. }
        | Sentence::SortDeclaration { attributes, .. }
        | Sentence::SymbolDeclaration { attributes, .. } => attributes.0.iter().collect(),
        Sentence::AliasDeclaration {
            left,
            right,
            attributes,
            ..
        } => {
            let mut patterns = vec![left.as_ref(), right.as_ref()];
            patterns.extend(attributes.0.iter());
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
            let mut patterns = vec![pattern.as_ref()];
            patterns.extend(attributes.0.iter());
            patterns
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

fn sentence_multiset(sentences: &[Sentence]) -> BTreeMap<String, usize> {
    let mut result = BTreeMap::new();
    for sentence in sentences {
        *result.entry(format!("{sentence:?}")).or_default() += 1;
    }
    result
}

fn difference(
    left: &BTreeMap<String, usize>,
    right: &BTreeMap<String, usize>,
) -> Vec<(String, usize)> {
    left.iter()
        .filter_map(|(sentence, left_count)| {
            let count = left_count.saturating_sub(right.get(sentence).copied().unwrap_or_default());
            (count != 0).then(|| (sentence.clone(), count))
        })
        .collect()
}

fn format_difference(
    reference_count: usize,
    actual_count: usize,
    missing: &[(String, usize)],
    extra: &[(String, usize)],
) -> String {
    const LIMIT: usize = 8;
    let mut output = format!(
        "KORE sentence multisets differ: reference={reference_count}, native={actual_count}, missing={}, extra={}",
        missing.iter().map(|(_, count)| count).sum::<usize>(),
        extra.iter().map(|(_, count)| count).sum::<usize>()
    );
    for (side, values) in [("missing", missing), ("extra", extra)] {
        for (sentence, count) in values.iter().take(LIMIT) {
            output.push_str(&format!("\n{side} x{count}: {sentence}"));
        }
        if values.len() > LIMIT {
            output.push_str(&format!("\n{side}: {} more distinct sentences", values.len() - LIMIT));
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::kore::ast::Symbol;

    fn sort() -> Sort {
        Sort::Application {
            name: "SortS".to_owned(),
            arguments: Vec::new(),
        }
    }

    fn application(name: &str, arguments: Vec<Pattern>) -> Pattern {
        Pattern::Application {
            symbol: Symbol {
                name: name.to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments,
        }
    }

    fn projector_declaration(name: &str) -> Sentence {
        Sentence::SymbolDeclaration {
            hooked: false,
            symbol: Symbol {
                name: name.to_owned(),
                sort_parameters: Vec::new(),
            },
            argument_sorts: vec![sort()],
            result_sort: sort(),
            attributes: Attributes(vec![application("function", Vec::new())]),
        }
    }

    fn projector_equation(name: &str) -> Sentence {
        Sentence::Axiom {
            parameters: vec!["R".to_owned()],
            pattern: Box::new(Pattern::Implies {
                sort: Sort::Variable("R".to_owned()),
                left: Box::new(Pattern::Top {
                    sort: Sort::Variable("R".to_owned()),
                }),
                right: Box::new(Pattern::Equals {
                    operand_sort: sort(),
                    result_sort: Sort::Variable("R".to_owned()),
                    left: Box::new(application(
                        name,
                        vec![Pattern::Variable(Variable {
                            kind: VariableKind::Element,
                            name: "X".to_owned(),
                            sort: sort(),
                        })],
                    )),
                    right: Box::new(Pattern::Top { sort: sort() }),
                }),
            }),
            attributes: Attributes::default(),
        }
    }

    fn module(sentences: Vec<Sentence>) -> Module {
        Module {
            name: "M".to_owned(),
            sentences,
            attributes: Attributes::default(),
        }
    }

    #[test]
    fn removes_only_complete_closed_unused_projector_pairs() {
        let name = "Lblproject'Coln'box'Coln'value";
        let mut module = module(vec![projector_declaration(name), projector_equation(name)]);
        assert_eq!(remove_closed_projector_pairs(&mut module, "test").unwrap(), 1);
        assert!(module.sentences.is_empty());
    }

    #[test]
    fn rejects_lone_declaration() {
        let name = "Lblproject'Coln'box'Coln'value";
        let mut module = module(vec![projector_declaration(name)]);
        let error = remove_closed_projector_pairs(&mut module, "test").unwrap_err();
        assert!(error.to_string().contains("exactly one generated equation"));
    }

    #[test]
    fn rejects_lone_equation() {
        let name = "Lblproject'Coln'box'Coln'value";
        let mut module = module(vec![projector_equation(name)]);
        let error = remove_closed_projector_pairs(&mut module, "test").unwrap_err();
        assert!(error.to_string().contains("exactly one unhooked declaration"));
    }

    #[test]
    fn rejects_reference_from_retained_sentence() {
        let name = "Lblproject'Coln'box'Coln'value";
        let mut module = module(vec![
            projector_declaration(name),
            projector_equation(name),
            Sentence::Axiom {
                parameters: Vec::new(),
                pattern: Box::new(application(name, vec![Pattern::Top { sort: sort() }])),
                attributes: Attributes::default(),
            },
        ]);
        let error = remove_closed_projector_pairs(&mut module, "test").unwrap_err();
        assert!(error.to_string().contains("not closed and unused"));
    }

    #[test]
    fn generic_project_prefix_is_not_an_allowance() {
        let malformed = "Lblproject'Coln'box";
        let mut module = module(vec![projector_declaration(malformed)]);
        assert_eq!(remove_closed_projector_pairs(&mut module, "test").unwrap(), 0);
        assert_eq!(module.sentences.len(), 1);
    }
}
