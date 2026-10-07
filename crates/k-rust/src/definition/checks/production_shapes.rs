//! This Java-compatible definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Production and configuration shape checks.

use std::collections::{BTreeMap, BTreeSet};

use super::{ProductionItem, Sentence};
use crate::definition::AttributeKey;
use crate::definition::{ProductionCatalog, ResolvedModule, SortCatalog, SortHead};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{GeneratedLabel, Sort, Term};
use crate::names::BuiltinSort;

const CELL_BAG_MESSAGE: &str = "Cell bags are only supported on the Java backend. If you want this feature, comment on https://github.com/runtimeverification/k/issues/1419 . As a workaround, you can add the attribute type=\"Set\" and add a unique identifier to each element in the set.";

/// The collection hooks a cell collection sort can carry: the multiplicity-`*` cell types.
const CELL_COLLECTION_HOOKS: [&str; 4] = ["LIST.List", "SET.Set", "MAP.Map", "BAG.Bag"];

/// Reject a `cell` or `cellCollection` attribute on a sentence that does not have the shape the
/// attribute asserts.
///
/// Configurations generate these sentences, and a definition may also spell them out (an
/// expanded definition, or a parse-only cell such as `generatedCounter`). Every consumer reads
/// the attribute as that shape: a `cell` production is the cell `"<name>" Sort* "</name>"`,
/// whose first and last items open and close one cell name and whose other items are the sorts
/// of its contents; a `cellCollection` sort is the hooked collection of a multiplicity-`*`
/// cell's instances; a `cellCollection` production is that sort's concatenation `S ::= S S`.
/// On any other sentence the attribute claims what the sentence is not, so it is reported here,
/// at load, before a rule or configuration grammar reads the sentence as a cell.
pub fn check_cell_attributes(module: &ResolvedModule, sorts: &SortCatalog<'_>) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in module.local_sentences.iter().map(std::sync::Arc::as_ref) {
        match sentence {
            Sentence::Production {
                sort,
                items,
                attributes,
                ..
            } => {
                if attributes.has(AttributeKey::Cell) && cell_name(items).is_none() {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidAttribute,
                        "The attribute 'cell' applies only to a cell production \"<name>\" Sort* \"</name>\", whose first and last terminals open and close one cell name and whose other items are the sorts of the cell's contents; this production is not one.",
                        sentence,
                    ));
                }
                if attributes.has(AttributeKey::CellCollection)
                    && !(is_concatenation(sort, items) && is_cell_collection(sort, sorts))
                {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidAttribute,
                        format!(
                            "The attribute 'cellCollection' applies only to the concatenation S ::= S S of a sort S declared with 'cellCollection'; this production of {sort} is not one."
                        ),
                        sentence,
                    ));
                }
            }
            Sentence::SyntaxSort {
                sort, attributes, ..
            } if attributes.has(AttributeKey::CellCollection) => {
                let hook = sorts
                    .attributes_for(&SortHead::from(sort))
                    .and_then(|attributes| attributes.string(AttributeKey::Hook));
                if !hook.is_some_and(|hook| CELL_COLLECTION_HOOKS.contains(&hook)) {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidAttribute,
                        format!(
                            "Sort {sort} has the attribute 'cellCollection' but no collection hook ({}): a cell collection sort is the hooked collection of a multiplicity-* cell's instances.",
                            CELL_COLLECTION_HOOKS.join(", ")
                        ),
                        sentence,
                    ));
                }
            }
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => {}
        }
    }
    diagnostics
}

/// The cell name of a cell production's items `"<name>" Sort* "</name>"`, or `None` for items
/// of another shape.
fn cell_name(items: &[ProductionItem]) -> Option<&str> {
    let [
        ProductionItem::Terminal(open),
        contents @ ..,
        ProductionItem::Terminal(close),
    ] = items
    else {
        return None;
    };
    let name = open.strip_prefix('<')?.strip_suffix('>')?;
    let closes = close
        .strip_prefix("</")
        .and_then(|close| close.strip_suffix('>'))
        == Some(name);
    (closes
        && !name.is_empty()
        && !name.starts_with('/')
        && contents
            .iter()
            .all(|item| matches!(item, ProductionItem::NonTerminal { .. })))
    .then_some(name)
}

fn is_concatenation(sort: &Sort, items: &[ProductionItem]) -> bool {
    matches!(
        items,
        [
            ProductionItem::NonTerminal { sort: left, .. },
            ProductionItem::NonTerminal { sort: right, .. },
        ] if left == sort && right == sort
    )
}

fn is_cell_collection(sort: &Sort, sorts: &SortCatalog<'_>) -> bool {
    sorts
        .attributes_for(&SortHead::from(sort))
        .is_some_and(|attributes| attributes.has(AttributeKey::CellCollection))
}

/// Java `CheckHOLE`.
pub fn check_holes(sentences: &[&Sentence]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        match sentence {
            Sentence::Production {
                items, attributes, ..
            } => {
                for attribute in [AttributeKey::Strict, AttributeKey::Seqstrict] {
                    let Some(value) = attributes.string(attribute) else {
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
                            .is_some_and(|sort| sort.name == BuiltinSort::K.k_name())
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
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => {}
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
    let list = Sort::builtin(BuiltinSort::List);
    for sentence in sentences {
        let Sentence::Production {
            items, attributes, ..
        } = sentence
        else {
            continue;
        };
        if !attributes.has(AttributeKey::Cell) || !attributes.has(AttributeKey::Stream) {
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
        if !attributes.has(AttributeKey::Cell) {
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
        if attributes.string(AttributeKey::Multiplicity) == Some("*")
            && attributes.string(AttributeKey::Type).unwrap_or("Bag") == "Bag"
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
    let components = split_without_trailing_empty_pieces(value, ';');
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
    let values = split_without_trailing_empty_pieces(value, ',');
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

fn split_without_trailing_empty_pieces(value: &str, separator: char) -> Vec<&str> {
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
            if label.generated()
                == Some(GeneratedLabel::SemanticCast {
                    sort_text: BuiltinSort::K.k_name(),
                })
                && matches!(arguments.as_slice(), [argument]
                    if matches!(argument.unannotated(), Term::Variable { name, .. } if name == "HOLE"))
    )
}

fn visible_cell_labels(productions: &ProductionCatalog<'_>) -> BTreeMap<Sort, String> {
    let mut labels = BTreeMap::new();
    for (_, production) in productions.productions() {
        let Sentence::Production {
            label: Some(label),
            sort,
            attributes,
            ..
        } = production
        else {
            continue;
        };
        if attributes.has(AttributeKey::Cell) {
            labels
                .entry(sort.clone())
                .or_insert_with(|| label.name.clone());
        }
    }
    labels
}
