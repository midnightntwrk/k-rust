//! Fail-closed native/reference KORE comparison for the M4 complete-IMP gate.
//!
//! The comparator canonicalizes constructor-tagged no-confusion pairs and no-junk alternatives whose order differs between K's `Production.ord` and k-rust's declaration order.
//! Its only exclusion beyond metadata and per-sentence alpha normalization is a mechanically proven, complete, closed, unused pair made from one structured-adapter named projector declaration and its one defining equation.
//! A projector-looking prefix is never sufficient.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};

use k_rust::kore::ast::{
    Attributes, Module, Pattern, Sentence, Sort, Symbol, Variable, VariableKind,
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
///
/// # Errors
///
/// Returns an error when either definition is malformed, the named module is
/// not unique, a fail-closed normalization condition is violated, or the
/// normalized sentence multisets differ.
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
    let reference = select_module(&reference.modules, module_name, "reference")?;
    let actual = select_module(&actual.modules, module_name, "native")?;

    compare_modules(reference, actual, policy)
}

/// Compare a native definition that embeds claims against an executable
/// reference definition plus the separately compiled reference specification.
///
/// # Errors
///
/// Returns an error under the same conditions as [`compare_kore`], or when the
/// reference specification does not contain exactly one import of the named
/// semantic module and one or more claims.
pub fn compare_kore_with_reference_claims(
    reference_source: &str,
    reference_claims_source: &str,
    reference_claims_module: &str,
    actual_source: &str,
    module_name: &str,
    policy: &ComparePolicy,
) -> Result<ComparisonReport, CompareError> {
    if module_name.is_empty() || reference_claims_module.is_empty() {
        return Err(CompareError::new(
            "module and reference claims module names must not be empty",
        ));
    }
    let reference = parse_definition(reference_source)
        .map_err(|error| CompareError::new(format!("cannot parse reference KORE: {error}")))?;
    let claims = parse_definition(reference_claims_source).map_err(|error| {
        CompareError::new(format!("cannot parse reference claims KORE: {error}"))
    })?;
    let actual = parse_definition(actual_source)
        .map_err(|error| CompareError::new(format!("cannot parse native KORE: {error}")))?;
    let mut reference = select_module(&reference.modules, module_name, "reference")?;
    let claims = select_module(&claims.modules, reference_claims_module, "reference claims")?;
    let actual = select_module(&actual.modules, module_name, "native")?;
    merge_reference_claims(&mut reference, claims, module_name)?;

    compare_modules(reference, actual, policy)
}

fn merge_reference_claims(
    reference: &mut Module,
    claims_module: Module,
    module_name: &str,
) -> Result<(), CompareError> {
    let mut imports = 0_usize;
    let mut claims = Vec::new();
    for sentence in claims_module.sentences {
        match sentence {
            Sentence::Import { module, .. } if module == module_name => imports += 1,
            Sentence::Import { module, .. } => {
                return Err(CompareError::new(format!(
                    "reference claims module imports unexpected module {module:?}"
                )));
            }
            sentence @ Sentence::Claim { .. } => claims.push(sentence),
            _ => {
                return Err(CompareError::new(
                    "reference claims module contains a non-import, non-claim sentence",
                ));
            }
        }
    }
    if imports != 1 {
        return Err(CompareError::new(format!(
            "reference claims module must import {module_name:?} exactly once; found {imports}"
        )));
    }
    if claims.is_empty() {
        return Err(CompareError::new(
            "reference claims module contains no claims",
        ));
    }
    reference.sentences.extend(claims);
    Ok(())
}

fn compare_modules(
    mut reference: Module,
    mut actual: Module,
    policy: &ComparePolicy,
) -> Result<ComparisonReport, CompareError> {
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

fn select_module(modules: &[Module], name: &str, route: &str) -> Result<Module, CompareError> {
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
                        // The source frontend copies this keyword metadata
                        // onto generated axioms. Symbol identity remains
                        // exact in declarations and patterns on both routes.
                        | "symbol'Kywd'"
                        // The structured frontend retains this context-alias
                        // marker on the generated cool rule after using it;
                        // the source frontend consumes and removes it.
                        | "cool-like"
                        // Native claims state this explicitly because they do
                        // not inherit kprove's all-path spec-module default.
                        // The compiled weakAlwaysFinally pattern remains exact.
                        | "all-path"
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
            return Err(CompareError::new(
                "label attribute is not exactly one string",
            ));
        };
        if let Some(mapped) = policy.label_map.get(label) {
            *label = mapped.clone();
        }
    }
    attributes.0.sort();
    Ok(())
}

fn alpha_normalize_sentence(sentence: &mut Sentence) {
    canonicalize_no_junk_axiom(sentence);
    canonicalize_no_confusion_pair(sentence);
    let mut names = BTreeMap::<(VariableKind, String, Sort), String>::new();
    for pattern in sentence_patterns_mut(sentence) {
        normalize_commuting_exists(pattern);
        alpha_normalize_pattern(pattern, &mut names);
    }
}

/// Canonicalize the commutative alternatives in one generated constructor no-junk axiom.
///
/// Each constructor alternative owns its existential binders.
/// Normalize those local names before ordering the alternatives so declaration order and `Production.ord` produce the same exact multiset member while retaining every alternative and its complete structure.
fn canonicalize_no_junk_axiom(sentence: &mut Sentence) {
    let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        return;
    };
    if !has_constructor_marker(attributes) {
        return;
    }
    let Pattern::Or { arguments, .. } = pattern.as_mut() else {
        return;
    };
    for argument in arguments.iter_mut() {
        normalize_commuting_exists(argument);
        alpha_normalize_pattern(argument, &mut BTreeMap::new());
    }
    arguments.sort();
}

/// Canonicalize the commutative constructor pair in one generated no-confusion axiom.
///
/// K orders the pair by `Production.ord`, while current k-rust uses declaration order.
/// The conjunction is commutative and its generated free variables are alpha-equivalent, so the comparator orders the applications by symbol and argument sorts before its ordinary per-sentence alpha normalization.
fn canonicalize_no_confusion_pair(sentence: &mut Sentence) {
    let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        return;
    };
    if !has_constructor_marker(attributes) {
        return;
    }
    let Pattern::Not { argument, .. } = pattern.as_mut() else {
        return;
    };
    let Pattern::And { arguments, .. } = argument.as_mut() else {
        return;
    };
    if arguments.len() != 2 || !arguments.iter().all(is_application_over_variables) {
        return;
    }
    arguments.sort_by_cached_key(no_confusion_conjunct_key);
    for (side, conjunct) in arguments.iter_mut().enumerate() {
        let Pattern::Application { arguments, .. } = conjunct else {
            unreachable!("no-confusion conjunct shape was checked")
        };
        for (position, argument) in arguments.iter_mut().enumerate() {
            let Pattern::Variable(variable) = argument else {
                unreachable!("no-confusion argument shape was checked")
            };
            variable.name = format!("NoConfusionSide{side}Arg{position}");
        }
    }
}

fn has_constructor_marker(attributes: &Attributes) -> bool {
    attributes.0.iter().any(|attribute| {
        matches!(
            attribute,
            Pattern::Application { symbol, arguments }
                if symbol.name == "constructor" && arguments.is_empty()
        )
    })
}

fn is_application_over_variables(pattern: &Pattern) -> bool {
    matches!(
        pattern,
        Pattern::Application { arguments, .. }
            if arguments.iter().all(|argument| matches!(argument, Pattern::Variable(_)))
    )
}

fn no_confusion_conjunct_key(pattern: &Pattern) -> (Symbol, Vec<Sort>) {
    let Pattern::Application { symbol, arguments } = pattern else {
        unreachable!("only applications over variables are keyed")
    };
    let sorts = arguments
        .iter()
        .map(|argument| match argument {
            Pattern::Variable(variable) => variable.sort.clone(),
            _ => unreachable!("only applications over variables are keyed"),
        })
        .collect();
    (symbol.clone(), sorts)
}

/// Normalize one standalone proof-result pattern using the same reviewed
/// variable policy as the native/reference sentence comparator.
///
/// Adjacent existential binders commute; all remaining structure is exact.
pub fn normalize_standalone_pattern(pattern: &mut Pattern) {
    normalize_commuting_exists(pattern);
    alpha_normalize_pattern(pattern, &mut BTreeMap::new());
}

fn normalize_commuting_exists(pattern: &mut Pattern) {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                normalize_commuting_exists(argument);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => normalize_commuting_exists(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            normalize_commuting_exists(left);
            normalize_commuting_exists(right);
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => normalize_commuting_exists(body),
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }

    if matches!(pattern, Pattern::Exists { .. }) {
        let mut binders = Vec::new();
        let mut current = &*pattern;
        while let Pattern::Exists { variable, body, .. } = current {
            binders.push(variable.clone());
            current = body;
        }
        // Adjacent existential quantifiers commute in KORE because sorts are
        // non-dependent. Sort only by kind and sort, retaining source order
        // for indistinguishable binder classes, before alpha normalization.
        binders.sort_by(|left, right| (left.kind, &left.sort).cmp(&(right.kind, &right.sort)));
        let mut current = pattern;
        for binder in binders {
            let Pattern::Exists { variable, body, .. } = current else {
                unreachable!("binder count came from this existential prefix")
            };
            *variable = binder;
            current = body;
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
    variable.name.clone_from(
        names
            .entry(key)
            .or_insert_with(|| format!("VarAlpha{next}")),
    );
}

fn remove_closed_projector_pairs(module: &mut Module, route: &str) -> Result<usize, CompareError> {
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
        for forbidden in ["priority", "owise"] {
            if has_attribute(attributes, forbidden) {
                return Err(CompareError::new(format!(
                    "{route} claim carries forbidden {forbidden:?} metadata"
                )));
            }
        }
        let label = string_attribute(attributes, "label")?
            .ok_or_else(|| CompareError::new(format!("{route} claim has no exact string label")))?;
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
            write!(output, "\n{side} x{count}: {sentence}")
                .expect("writing to a String cannot fail");
        }
        if values.len() > LIMIT {
            write!(
                output,
                "\n{side}: {} more distinct sentences",
                values.len() - LIMIT
            )
            .expect("writing to a String cannot fail");
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(
            remove_closed_projector_pairs(&mut module, "test").unwrap(),
            1
        );
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
        assert!(
            error
                .to_string()
                .contains("exactly one unhooked declaration")
        );
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
        assert_eq!(
            remove_closed_projector_pairs(&mut module, "test").unwrap(),
            0
        );
        assert_eq!(module.sentences.len(), 1);
    }

    #[test]
    fn source_frontend_markers_are_nonsemantic_metadata() {
        let mut attributes = Attributes(vec![
            application(
                "symbol'Kywd'",
                vec![Pattern::String("source-spelling".to_owned())],
            ),
            application("cool-like", Vec::new()),
            application("all-path", Vec::new()),
        ]);
        normalize_attributes(&mut attributes);
        assert!(attributes.0.is_empty());
    }

    #[test]
    fn commuting_existential_prefixes_normalize_identically() {
        fn named_sort(name: &str) -> Sort {
            Sort::Application {
                name: name.to_owned(),
                arguments: Vec::new(),
            }
        }

        let int = Variable {
            kind: VariableKind::Element,
            name: "Counter".to_owned(),
            sort: named_sort("SortInt"),
        };
        let value = Variable {
            kind: VariableKind::Element,
            name: "Result".to_owned(),
            sort: named_sort("SortValue"),
        };
        let body = application(
            "pair",
            vec![
                Pattern::Variable(int.clone()),
                Pattern::Variable(value.clone()),
            ],
        );
        let prefix = |outer: Variable, inner: Variable| Pattern::Exists {
            sort: sort(),
            variable: outer,
            body: Box::new(Pattern::Exists {
                sort: sort(),
                variable: inner,
                body: Box::new(body.clone()),
            }),
        };
        let mut reference = prefix(value.clone(), int.clone());
        let mut native = prefix(int, value);

        normalize_commuting_exists(&mut reference);
        normalize_commuting_exists(&mut native);
        let mut reference_names = BTreeMap::new();
        let mut native_names = BTreeMap::new();
        alpha_normalize_pattern(&mut reference, &mut reference_names);
        alpha_normalize_pattern(&mut native, &mut native_names);

        assert_eq!(reference, native);
    }

    #[test]
    fn commutative_no_confusion_pairs_normalize_identically() {
        fn variable(name: &str) -> Pattern {
            Pattern::Variable(Variable {
                kind: VariableKind::Element,
                name: name.to_owned(),
                sort: sort(),
            })
        }

        fn no_confusion(left: Pattern, right: Pattern) -> Sentence {
            Sentence::Axiom {
                parameters: Vec::new(),
                pattern: Box::new(Pattern::Not {
                    sort: sort(),
                    argument: Box::new(Pattern::And {
                        sort: sort(),
                        arguments: vec![left, right],
                    }),
                }),
                attributes: Attributes(vec![application("constructor", Vec::new())]),
            }
        }

        let pair = application("pair", vec![variable("X"), variable("Y")]);
        let zero = application("zero", Vec::new());
        let mut reference = no_confusion(pair.clone(), zero.clone());
        let mut native = no_confusion(zero, pair);

        alpha_normalize_sentence(&mut reference);
        alpha_normalize_sentence(&mut native);

        assert_eq!(reference, native);
    }

    #[test]
    fn commutative_no_junk_alternatives_normalize_identically() {
        fn alternative(name: &str, variable_name: &str) -> Pattern {
            let variable = Variable {
                kind: VariableKind::Element,
                name: variable_name.to_owned(),
                sort: sort(),
            };
            Pattern::Exists {
                sort: sort(),
                variable: variable.clone(),
                body: Box::new(application(name, vec![Pattern::Variable(variable)])),
            }
        }

        fn no_junk(arguments: Vec<Pattern>) -> Sentence {
            Sentence::Axiom {
                parameters: Vec::new(),
                pattern: Box::new(Pattern::Or {
                    sort: sort(),
                    arguments,
                }),
                attributes: Attributes(vec![application("constructor", Vec::new())]),
            }
        }

        let bottom = Pattern::Bottom { sort: sort() };
        let mut reference = no_junk(vec![
            alternative("left", "X"),
            alternative("right", "Y"),
            bottom.clone(),
        ]);
        let mut native = no_junk(vec![
            bottom,
            alternative("right", "Other"),
            alternative("left", "Value"),
        ]);

        alpha_normalize_sentence(&mut reference);
        alpha_normalize_sentence(&mut native);

        assert_eq!(reference, native);
    }
}
