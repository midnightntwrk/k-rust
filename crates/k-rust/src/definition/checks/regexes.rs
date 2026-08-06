//! Semantic validation ported from Java `CheckRegex`.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use super::Sentence;
use crate::definition::ProductionItem;
use crate::definition::regex::{CharClass, Regex, RegexBody, parse};
use crate::diagnostic::{Diagnostic, DiagnosticCode};

pub fn check_regexes(local: &[&Sentence], visible: &[&Sentence]) -> Vec<Diagnostic> {
    let declarations = visible
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::SyntaxLexical { name, .. } => Some((name.clone(), *sentence)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let mut dependencies = BTreeMap::<String, BTreeSet<String>>::new();
    let mut diagnostics = Vec::new();

    for sentence in local {
        let mut parsed = Vec::new();
        match sentence {
            Sentence::SyntaxLexical { name, regex, .. } => match parse(regex) {
                Ok(regex) => {
                    dependencies.insert(
                        name.clone(),
                        named_references(&regex.body).into_iter().collect(),
                    );
                    if regex.start_line || regex.end_line {
                        diagnostics.push(invalid_regex(
                            "Named lexical syntax cannot contain line anchors.",
                            sentence,
                        ));
                    }
                    parsed.push(regex);
                }
                Err(error) => diagnostics.push(invalid_regex(error.to_string(), sentence)),
            },
            Sentence::Production { items, .. } => {
                for regex in items.iter().filter_map(|item| match item {
                    ProductionItem::RegexTerminal { regex, .. } => Some(regex),
                    ProductionItem::NonTerminal { .. } | ProductionItem::Terminal(_) => None,
                }) {
                    match parse(regex) {
                        Ok(regex) => parsed.push(regex),
                        Err(error) => diagnostics.push(invalid_regex(error.to_string(), sentence)),
                    }
                }
            }
            _ => continue,
        }

        let mut bad_names = Vec::new();
        for name in parsed
            .iter()
            .flat_map(|regex| named_references(&regex.body))
            .filter(|name| !declarations.contains_key(name))
        {
            if !bad_names.contains(&name) {
                bad_names.push(name);
            }
        }
        if !bad_names.is_empty() {
            diagnostics.push(invalid_regex(
                format!(
                    "Unrecognized lexical identifiers in regular expression: [{}]",
                    bad_names.join(", ")
                ),
                sentence,
            ));
        }
        check_parsed_regexes(&parsed, sentence, &mut diagnostics);
    }

    for mut cycle in disjoint_cycles(dependencies) {
        rotate_cycle(&mut cycle, &declarations);
        let sentence = declarations
            .get(&cycle[0])
            .expect("cycle members are lexical declarations");
        diagnostics.push(invalid_regex(
            format!(
                "Circular dependency between lexical identifiers: [{}]",
                cycle.join(", ")
            ),
            sentence,
        ));
    }
    diagnostics
}

fn check_parsed_regexes(regexes: &[Regex], sentence: &Sentence, diagnostics: &mut Vec<Diagnostic>) {
    let mut negated_unicode = Vec::new();
    let mut range_unicode = Vec::new();
    for regex in regexes {
        regex.body.visit_preorder(&mut |body| match body {
            RegexBody::CharClass { negated, members } => {
                for member in members {
                    match member {
                        CharClass::Char(character) if *negated && !character.is_ascii() => {
                            push_unique(&mut negated_unicode, *character);
                        }
                        CharClass::Range { start, end } => {
                            if *negated {
                                for character in [*start, *end]
                                    .into_iter()
                                    .filter(|character| !character.is_ascii())
                                {
                                    push_unique(&mut negated_unicode, character);
                                }
                            }
                            for character in [*start, *end]
                                .into_iter()
                                .filter(|character| !character.is_ascii())
                            {
                                push_unique(&mut range_unicode, character);
                            }
                            if start > end {
                                diagnostics.push(invalid_regex(
                                    format!(
                                        "Invalid character range '{}'. Start of range U+{:04X} is greater than end of range U+{:04X}.",
                                        member,
                                        *start as u32,
                                        *end as u32
                                    ),
                                    sentence,
                                ));
                            }
                        }
                        CharClass::Char(_) => {}
                    }
                }
            }
            RegexBody::Range {
                at_least,
                at_most,
                ..
            } if at_least > at_most => diagnostics.push(invalid_regex(
                format!(
                    "Invalid numeric range '{}'. Start of range {at_least} is greater than end of range {at_most}.",
                    body
                ),
                sentence,
            )),
            _ => {}
        });
    }
    if !negated_unicode.is_empty() {
        diagnostics.push(invalid_regex(
            format!(
                "Unsupported non-ASCII characters found in negated character class: [{}]",
                negated_unicode
                    .into_iter()
                    .map(|character| character.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            sentence,
        ));
    }
    if !range_unicode.is_empty() {
        diagnostics.push(invalid_regex(
            format!(
                "Unsupported non-ASCII characters found in character class range: [{}]",
                range_unicode
                    .into_iter()
                    .map(|character| character.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            sentence,
        ));
    }
}

fn named_references(body: &RegexBody) -> Vec<String> {
    let mut names = Vec::new();
    body.visit_preorder(&mut |body| {
        if let RegexBody::Named(name) = body
            && !names.contains(name)
        {
            names.push(name.clone());
        }
    });
    names
}

fn push_unique<T: PartialEq>(values: &mut Vec<T>, value: T) {
    if !values.contains(&value) {
        values.push(value);
    }
}

fn disjoint_cycles(mut adjacency: BTreeMap<String, BTreeSet<String>>) -> Vec<Vec<String>> {
    let mut cycles = Vec::new();
    while let Some(cycle) = find_cycle(&adjacency) {
        let members = cycle.iter().cloned().collect::<BTreeSet<_>>();
        adjacency.retain(|name, _| !members.contains(name));
        for dependencies in adjacency.values_mut() {
            dependencies.retain(|name| !members.contains(name));
        }
        cycles.push(cycle);
    }
    cycles
}

fn find_cycle(adjacency: &BTreeMap<String, BTreeSet<String>>) -> Option<Vec<String>> {
    let mut visited = BTreeSet::new();
    let mut stack = Vec::new();
    let mut on_stack = BTreeMap::<String, usize>::new();
    for name in adjacency.keys() {
        if let Some(cycle) = visit_cycle(name, adjacency, &mut visited, &mut stack, &mut on_stack) {
            return Some(cycle);
        }
    }
    None
}

fn visit_cycle(
    name: &str,
    adjacency: &BTreeMap<String, BTreeSet<String>>,
    visited: &mut BTreeSet<String>,
    stack: &mut Vec<String>,
    on_stack: &mut BTreeMap<String, usize>,
) -> Option<Vec<String>> {
    if let Some(&start) = on_stack.get(name) {
        return Some(stack[start..].to_vec());
    }
    if !visited.insert(name.to_owned()) {
        return None;
    }
    on_stack.insert(name.to_owned(), stack.len());
    stack.push(name.to_owned());
    for dependency in adjacency.get(name).into_iter().flatten() {
        if let Some(cycle) = visit_cycle(dependency, adjacency, visited, stack, on_stack) {
            return Some(cycle);
        }
    }
    stack.pop();
    on_stack.remove(name);
    None
}

fn rotate_cycle(cycle: &mut [String], declarations: &BTreeMap<String, &Sentence>) {
    let first = cycle
        .iter()
        .enumerate()
        .min_by(|(_, left), (_, right)| {
            compare_locations(declarations[left.as_str()], declarations[right.as_str()])
        })
        .map_or(0, |(index, _)| index);
    cycle.rotate_left(first);
}

fn compare_locations(left: &Sentence, right: &Sentence) -> Ordering {
    compare_optional_last(left.attributes().source(), right.attributes().source()).then_with(|| {
        compare_optional_last(left.attributes().location(), right.attributes().location())
    })
}

fn compare_optional_last<T: Ord>(left: Option<T>, right: Option<T>) -> Ordering {
    match (left, right) {
        (Some(left), Some(right)) => left.cmp(&right),
        (Some(_), None) => Ordering::Less,
        (None, Some(_)) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    }
}

fn invalid_regex(message: impl Into<String>, sentence: &Sentence) -> Diagnostic {
    Diagnostic::error(DiagnosticCode::InvalidRegex, message, sentence)
}
