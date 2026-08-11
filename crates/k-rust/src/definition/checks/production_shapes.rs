//! Production and configuration shape checks.

use std::collections::{BTreeMap, BTreeSet};

use super::{ProductionItem, Sentence};
use crate::definition::ProductionCatalog;
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{Sort, Term};

const CELL_BAG_MESSAGE: &str = "Cell bags are only supported on the Java backend. If you want this feature, comment on https://github.com/runtimeverification/k/issues/1419 . As a workaround, you can add the attribute type=\"Set\" and add a unique identifier to each element in the set.";

/// Java `CheckHOLE`.
pub fn check_holes(sentences: &[&Sentence]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        match sentence {
            Sentence::Production {
                items, attributes, ..
            } => {
                for attribute in ["strict", "seqstrict"] {
                    let Some(value) = attributes.get_str(attribute) else {
                        continue;
                    };
                    let positions =
                        match strict_positions(value, nonterminal_count(items), sentence) {
                            Ok(positions) => positions,
                            Err(diagnostic) => {
                                diagnostics.push(diagnostic);
                                continue;
                            }
                        };
                    let nonterminals = items
                        .iter()
                        .filter_map(|item| match item {
                            ProductionItem::NonTerminal { sort, .. } => Some(sort),
                            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => {
                                None
                            }
                        })
                        .collect::<Vec<_>>();
                    for position in positions {
                        if nonterminals
                            .get(position - 1)
                            .is_some_and(|sort| sort.name == "K")
                        {
                            diagnostics.push(Diagnostic::error(
                                DiagnosticCode::InvalidHole,
                                "Cannot heat a nonterminal of sort K. Did you mean KItem?",
                                sentence,
                            ));
                        }
                    }
                }
            }
            Sentence::Context { body, .. } => body.visit_preorder(&mut |term| {
                if is_k_hole(term) {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidHole,
                        "Cannot heat a HOLE of sort K. Did you mean to sort it to KItem?",
                        sentence,
                    ));
                }
            }),
            _ => {}
        }
    }
    diagnostics
}

/// Java `CheckStreams`.
pub fn check_streams(
    sentences: &[&Sentence],
    subsorts: &crate::definition::PartialOrder<Sort>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let list = Sort::new("List");
    for sentence in sentences {
        let Sentence::Production {
            items, attributes, ..
        } = sentence
        else {
            continue;
        };
        if attributes.get("cell").is_none() || attributes.get("stream").is_none() {
            continue;
        }
        match items.get(1) {
            Some(ProductionItem::NonTerminal { sort, .. }) => {
                if !subsorts.less_than_eq(sort, &list) {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidStreamCell,
                        format!("Wrong sort in streaming cell. Expected List, but found {sort}."),
                        sentence,
                    ));
                }
            }
            _ => diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidStreamCell,
                "Illegal arguments for stream cell.",
                sentence,
            )),
        }
    }
    diagnostics
}

/// Java `CheckConfigurationCells`.
pub fn check_configuration_cells(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
) -> Vec<Diagnostic> {
    let cell_labels = visible_cell_labels(productions);
    let mut seen_cells = BTreeSet::new();
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let Sentence::Production {
            items, attributes, ..
        } = sentence
        else {
            continue;
        };
        if attributes.get("cell").is_none() {
            continue;
        }
        for item in items {
            let ProductionItem::NonTerminal { sort, .. } = item else {
                continue;
            };
            if sort.name.ends_with("Cell") && !seen_cells.insert(sort.clone()) {
                let name = cell_labels
                    .get(sort)
                    .map(String::as_str)
                    .unwrap_or(sort.name.as_str());
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::DuplicateConfigurationCell,
                    format!("Cell {name} found twice in configuration."),
                    sentence,
                ));
            }
        }
        if attributes.get_str("multiplicity") == Some("*")
            && attributes.get_str("type").unwrap_or("Bag") == "Bag"
        {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::UnsupportedCellBag,
                CELL_BAG_MESSAGE,
                sentence,
            ));
        }
    }
    diagnostics
}

fn strict_positions(
    value: &str,
    arity: usize,
    sentence: &Sentence,
) -> Result<Vec<usize>, Diagnostic> {
    if value.is_empty() {
        return Ok((1..=arity).collect());
    }
    let components = java_split(value, ';');
    if components.len() == 1 {
        let component = components[0].trim();
        if component.starts_with(|character: char| character.is_ascii_digit()) {
            return parse_positions(component, arity, sentence);
        }
        return Ok((1..=arity).collect());
    }
    if components.len().is_multiple_of(2) {
        let mut positions = Vec::new();
        for component in components.iter().skip(1).step_by(2) {
            positions.extend(parse_positions(component.trim(), arity, sentence)?);
        }
        return Ok(positions);
    }
    Err(Diagnostic::error(
        DiagnosticCode::InvalidStrictness,
        "Invalid strict attribute containing invalid semicolons. Must contain 0, 1, 2, or an even number of components.",
        sentence,
    ))
}

fn parse_positions(
    value: &str,
    arity: usize,
    sentence: &Sentence,
) -> Result<Vec<usize>, Diagnostic> {
    let values = java_split(value, ',');
    let display = format!("[{}]", values.join(", "));
    let mut positions = Vec::new();
    for value in values {
        let position = value.trim().parse::<usize>().ok();
        let Some(position) = position.filter(|position| *position >= 1 && *position <= arity)
        else {
            let message = if arity == 0 {
                "Cannot put a strict attribute on a production with no nonterminals".to_owned()
            } else {
                format!(
                    "Expecting a number between 1 and {arity}, but found {value} as a strict position in {display}"
                )
            };
            return Err(Diagnostic::error(
                DiagnosticCode::InvalidStrictness,
                message,
                sentence,
            ));
        };
        positions.push(position);
    }
    Ok(positions)
}

fn java_split(value: &str, separator: char) -> Vec<&str> {
    if value.is_empty() {
        return vec![""];
    }
    let mut values = value.split(separator).collect::<Vec<_>>();
    while values.last() == Some(&"") {
        values.pop();
    }
    values
}

fn nonterminal_count(items: &[ProductionItem]) -> usize {
    items
        .iter()
        .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
        .count()
}

fn is_k_hole(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Apply { label, arguments }
            if label.name == "#SemanticCastToK"
                && matches!(arguments.as_slice(), [argument]
                    if matches!(argument.unannotated(), Term::Variable { name, .. } if name == "HOLE"))
    )
}

fn visible_cell_labels(productions: &ProductionCatalog<'_>) -> BTreeMap<Sort, String> {
    let mut labels = BTreeMap::new();
    for (_, production) in productions.sorted_productions() {
        let Sentence::Production {
            label: Some(label),
            sort,
            attributes,
            ..
        } = production
        else {
            continue;
        };
        if attributes.get("cell").is_some() {
            labels
                .entry(sort.clone())
                .or_insert_with(|| label.name.clone());
        }
    }
    labels
}
